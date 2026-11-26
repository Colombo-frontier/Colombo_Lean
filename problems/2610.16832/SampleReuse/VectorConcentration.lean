import SampleReuse.OperatorConfidence

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace SampleReuse
noncomputable section
open Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A rank-two symmetric embedding. For a unit anchor its operator norm lies
between `‖v‖` and `2*‖v‖`, so it preserves concentration up to absolute constants. -/
def rankTwo (e v : E) : E →L[ℝ] E :=
  (innerSL ℝ e).smulRight v + (innerSL ℝ v).smulRight e

@[simp] theorem rankTwo_apply (e v x : E) :
    rankTwo e v x = ⟪e,x⟫_ℝ • v + ⟪v,x⟫_ℝ • e := rfl

theorem rankTwo_norm_le (e v : E) : ‖rankTwo e v‖ ≤ 2*‖e‖*‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [rankTwo_apply]
  calc
    _ ≤ ‖⟪e,x⟫_ℝ • v‖ + ‖⟪v,x⟫_ℝ • e‖ := norm_add_le _ _
    _ = ‖⟪e,x⟫_ℝ‖*‖v‖ + ‖⟪v,x⟫_ℝ‖*‖e‖ := by rw [norm_smul, norm_smul]
    _ ≤ (‖e‖*‖x‖)*‖v‖ + (‖v‖*‖x‖)*‖e‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (norm_inner_le_norm (𝕜 := ℝ) e x) (norm_nonneg v))
        (mul_le_mul_of_nonneg_right (norm_inner_le_norm (𝕜 := ℝ) v x) (norm_nonneg e))
    _ = _ := by ring

def rankTwoL (e : E) : E →L[ℝ] (E →L[ℝ] E) :=
  LinearMap.mkContinuous
    { toFun := rankTwo e
      map_add' := by
        intro v w
        ext x
        simp only [rankTwo_apply, ContinuousLinearMap.add_apply, inner_add_left,
          add_smul, smul_add]
        abel
      map_smul' := by
        intro c v
        ext x
        simp [rankTwo_apply, real_inner_smul_left, smul_add, smul_smul, mul_comm] }
    (2*‖e‖) (rankTwo_norm_le e)

@[simp] theorem rankTwoL_apply (e v : E) : rankTwoL e v = rankTwo e v := rfl

theorem rankTwo_symmetric (e v : E) : (rankTwo e v).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪rankTwo e v x,y⟫_ℝ = ⟪x,rankTwo e v y⟫_ℝ
  simp only [rankTwo_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x v, real_inner_comm x e]
  ring

theorem norm_le_rankTwo_norm (e : E) (he : ‖e‖ = 1) (v : E) :
    ‖v‖ ≤ ‖rankTwo e v‖ := by
  have ha : rankTwo e v e = v + ⟪v,e⟫_ℝ • e := by
    simp [rankTwo_apply, real_inner_self_eq_norm_sq, he]
  have hs : ‖rankTwo e v e‖^2 = ‖v‖^2 + 3*⟪v,e⟫_ℝ^2 := by
    rw [ha, norm_add_sq_real, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs]
    ring
  have hl : ‖v‖ ≤ ‖rankTwo e v e‖ := by
    nlinarith [sq_nonneg ⟪v,e⟫_ℝ, norm_nonneg v, norm_nonneg (rankTwo e v e)]
  exact hl.trans (by simpa [he] using (rankTwo e v).le_opNorm e)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual Hilbert-vector average concentration, using the rank-two embedding.
There is one logarithmic dimension factor and no coordinate union bound. -/
theorem independent_vector_average_confidence {n : ℕ}
    (X : Fin n → Ω → E) (hX : ∀ i, Measurable (X i))
    {σ η δ : ℝ} (hσ : 0 ≤ σ) (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n)
    (hb : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ σ)
    (hind : iIndepFun X μ) (hzero : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsize : 32*(matrixMomentOrder (Module.finrank ℝ E + 1) δ : ℝ)*σ^2 ≤
      (n:ℝ)*η^2) :
    μ.real {ω | η ≤ ‖(n:ℝ)⁻¹ • ∑ i, X i ω‖} ≤ δ := by
  by_cases hE : Nontrivial E
  · letI := hE
    let e : E := stdOrthonormalBasis ℝ E ⟨0, Module.finrank_pos⟩
    have he : ‖e‖ = 1 := (stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one _
    let A : Fin n → Ω → (E →L[ℝ] E) := fun i ω => rankTwo e (X i ω)
    have hA : ∀ i, Measurable (A i) := fun i => (rankTwoL e).continuous.measurable.comp (hX i)
    have hAb : ∀ i, ∀ᵐ ω ∂μ, ‖A i ω‖ ≤ 2*σ := by
      intro i
      filter_upwards [hb i] with ω hω
      exact (rankTwo_norm_le e (X i ω)).trans (by simpa [he] using mul_le_mul_of_nonneg_left hω (by norm_num : (0:ℝ) ≤ 2))
    have hAi : iIndepFun A μ := hind.comp (fun _ => rankTwoL e)
      (fun _ => (rankTwoL e).continuous.measurable)
    have hAm : ∀ i, (∫ ω, A i ω ∂μ) = 0 := by
      intro i
      have hi : Integrable (X i) μ := (integrable_const σ).mono' (hX i).aestronglyMeasurable (hb i)
      change (∫ ω, rankTwoL e (X i ω) ∂μ) = 0
      rw [(rankTwoL e).integral_comp_comm hi, hzero i, map_zero]
    have hAs : ∀ i, ∀ᵐ ω ∂μ, (A i ω).toLinearMap.IsSymmetric :=
      fun i => Filter.Eventually.of_forall fun ω => rankTwo_symmetric e (X i ω)
    have hsz : 8*(matrixMomentOrder (Module.finrank ℝ E + 1) δ : ℝ)*(2*σ)^2 ≤
        (n:ℝ)*η^2 := by nlinarith [hsize]
    have hc := independent_operator_average_confidence A hA (by positivity : 0 ≤ 2*σ)
      hη hδ hn hAb hAi hAm hAs hsz
    apply (measureReal_mono (μ := μ) (s₂ := {ω | η ≤ ‖(n:ℝ)⁻¹ • ∑ i, A i ω‖}) ?_).trans hc
    intro ω hω
    have hl := norm_le_rankTwo_norm e he ((n:ℝ)⁻¹ • ∑ i, X i ω)
    have heq : rankTwo e ((n:ℝ)⁻¹ • ∑ i, X i ω) =
        (n:ℝ)⁻¹ • ∑ i, A i ω := by
      change rankTwoL e ((n:ℝ)⁻¹ • ∑ i, X i ω) = _
      rw [map_smul, map_sum]
      rfl
    rw [heq] at hl
    exact le_trans hω hl
  · haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    have hempty : {ω | η ≤ ‖(n:ℝ)⁻¹ • ∑ i, X i ω‖} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro ω
      have hz : (n:ℝ)⁻¹ • ∑ i, X i ω = 0 := Subsingleton.elim _ _
      simpa [hz] using not_le_of_gt hη
    simpa [hempty] using hδ.le

end
end SampleReuse
