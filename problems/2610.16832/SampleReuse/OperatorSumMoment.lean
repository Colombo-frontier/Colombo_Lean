import SampleReuse.OperatorWordExpectation

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace SampleReuse
noncomputable section
open Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem trace_sum_pow_eq_words {n p : ℕ} (X : Fin n → (E →L[ℝ] E)) :
    opTrace ((∑ i, X i)^p) = ∑ w : Fin p → Fin n, opTrace (operatorWord X w) := by
  rw [sum_pow_eq_operatorWords]
  exact map_sum opTraceL _ _

omit [FiniteDimensional ℝ E] in
theorem opSymmetric_sum {ι : Type*} [Fintype ι] (A : ι → (E →L[ℝ] E))
    (ha : ∀ i, (A i).toLinearMap.IsSymmetric) :
    (∑ i, A i).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪(∑ i, A i) x, y⟫_ℝ = ⟪x, (∑ i, A i) y⟫_ℝ
  simp only [ContinuousLinearMap.sum_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl (fun i _ => (ha i).apply_clm x y)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} (X : Fin n → Ω → (E →L[ℝ] E)) (hX : ∀ i, Measurable (X i))
  {σ : ℝ} (hσ : 0 ≤ σ) (hb : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ σ)

include hX hσ hb

theorem trace_sum_pow_integrable (p : ℕ) :
    Integrable (fun ω => opTrace ((∑ i, X i ω)^p)) μ := by
  simp_rw [trace_sum_pow_eq_words]
  exact integrable_finset_sum _ (fun w _ => trace_operatorWord_integrable X hX w hσ hb)

theorem trace_operatorWord_integral_le {p : ℕ} (w : Fin p → Fin n) :
    (∫ ω, opTrace (operatorWord (fun i => X i ω) w) ∂μ) ≤
      (Module.finrank ℝ E : ℝ)*σ^p := by
  have hall : ∀ᵐ ω ∂μ, ∀ i, ‖X i ω‖ ≤ σ := ae_all_iff.mpr hb
  have hb' : ∀ᵐ ω ∂μ, opTrace (operatorWord (fun i => X i ω) w) ≤
      (Module.finrank ℝ E : ℝ)*σ^p := hall.mono fun ω hω =>
    (le_abs_self _).trans (abs_trace_operatorWord_le (fun i => X i ω) w hσ hω)
  simpa using integral_mono_ae (trace_operatorWord_integrable X hX w hσ hb)
    (integrable_const ((Module.finrank ℝ E : ℝ)*σ^p)) hb'

/-- The trace-even-moment bound for centered independent bounded random
operators under an arbitrary probability measure. No finite-support assumption
and no matrix concentration result is assumed. -/
theorem independent_operator_trace_even_moment
    (hind : iIndepFun X μ) (hzero : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    {k : ℕ} (hkn : k ≤ n) :
    (∫ ω, opTrace ((∑ i, X i ω)^(2*k)) ∂μ) ≤
      (Module.finrank ℝ E : ℝ) * (4*(k:ℝ)*(n:ℝ)*σ^2)^k := by
  let W := Finset.univ.filter (fun w : Fin (2*k) → Fin n => NoSingletonWord w)
  let I : (Fin (2*k) → Fin n) → ℝ :=
    fun w => ∫ ω, opTrace (operatorWord (fun i => X i ω) w) ∂μ
  have hvanish (w : Fin (2*k) → Fin n) (hw : ¬ NoSingletonWord w) : I w = 0 := by
    simp only [NoSingletonWord, not_forall, not_exists, not_and] at hw
    obtain ⟨j, hj⟩ := hw
    apply bounded_singleton_operatorWord_integral_zero X hX hind w j _ (hzero (w j)) hσ hb
    intro t ht
    by_contra hne
    exact hj t hne ht
  have heq : ∑ w ∈ W, I w = ∑ w, I w := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w _ hw
    apply hvanish
    simpa [W] using hw
  have hc : W.card ≤ (4*k*n)^k := by
    simpa only [Fintype.card_subtype, W] using (noSingletonWord_card_le hkn)
  have hcr : (W.card : ℝ) ≤ (4*(k:ℝ)*(n:ℝ))^k := by exact_mod_cast hc
  have hC : 0 ≤ (Module.finrank ℝ E : ℝ)*σ^(2*k) := by positivity
  calc
    _ = ∑ w : Fin (2*k) → Fin n, I w := by
      simp_rw [trace_sum_pow_eq_words]
      exact integral_finset_sum _ (fun w _ => trace_operatorWord_integrable X hX w hσ hb)
    _ = ∑ w ∈ W, I w := heq.symm
    _ ≤ ∑ _w ∈ W, (Module.finrank ℝ E : ℝ)*σ^(2*k) := by
      apply Finset.sum_le_sum
      intro w _
      exact trace_operatorWord_integral_le X hX hσ hb w
    _ = (W.card : ℝ)*((Module.finrank ℝ E : ℝ)*σ^(2*k)) := by simp
    _ ≤ (4*(k:ℝ)*(n:ℝ))^k*((Module.finrank ℝ E : ℝ)*σ^(2*k)) :=
      mul_le_mul_of_nonneg_right hcr hC
    _ = _ := by rw [pow_mul, mul_pow]; ring

theorem operator_sum_norm_even_integrable
    (hsym : ∀ i, ∀ᵐ ω ∂μ, (X i ω).toLinearMap.IsSymmetric)
    {k : ℕ} (hk : 0 < k) :
    Integrable (fun ω => ‖∑ i, X i ω‖^(2*k)) μ := by
  have hm : Measurable (fun ω => ∑ i, X i ω) :=
    Finset.measurable_sum _ (fun i _ => hX i)
  apply (trace_sum_pow_integrable X hX hσ hb (2*k)).mono'
    (hm.norm.pow_const (2*k)).aestronglyMeasurable
  have hsall : ∀ᵐ ω ∂μ, ∀ i, (X i ω).toLinearMap.IsSymmetric := ae_all_iff.mpr hsym
  filter_upwards [hsall] with ω hω
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact opNorm_even_pow_le_trace _ (opSymmetric_sum _ hω) hk

/-- Actual operator-norm moment; dimension enters only as the trace factor. -/
theorem independent_operator_norm_even_moment
    (hind : iIndepFun X μ) (hzero : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsym : ∀ i, ∀ᵐ ω ∂μ, (X i ω).toLinearMap.IsSymmetric)
    {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    (∫ ω, ‖∑ i, X i ω‖^(2*k) ∂μ) ≤
      (Module.finrank ℝ E : ℝ) * (4*(k:ℝ)*(n:ℝ)*σ^2)^k := by
  have hsall : ∀ᵐ ω ∂μ, ∀ i, (X i ω).toLinearMap.IsSymmetric := ae_all_iff.mpr hsym
  have hdom : ∀ᵐ ω ∂μ, ‖∑ i, X i ω‖^(2*k) ≤ opTrace ((∑ i, X i ω)^(2*k)) :=
    hsall.mono fun ω hω => opNorm_even_pow_le_trace _ (opSymmetric_sum _ hω) hk
  exact (integral_mono_ae (operator_sum_norm_even_integrable X hX hσ hb hsym hk)
    (trace_sum_pow_integrable X hX hσ hb (2*k)) hdom).trans
    (independent_operator_trace_even_moment X hX hσ hb hind hzero hkn)

end
end SampleReuse
