import SampleReuse.OperatorConcentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SampleReuse
noncomputable section
open Classical

def matrixMomentOrder (d : ℕ) (δ : ℝ) : ℕ :=
  ⌈Real.log ((d:ℝ)/δ) / Real.log 2⌉₊ + 1

theorem matrixMomentOrder_pos (d : ℕ) (δ : ℝ) : 0 < matrixMomentOrder d δ :=
  Nat.succ_pos _

theorem matrixMomentOrder_log (d : ℕ) (δ : ℝ) :
    Real.log ((d:ℝ)/δ) ≤ (matrixMomentOrder d δ : ℝ)*Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil (Real.log ((d:ℝ)/δ) / Real.log 2)
  apply (div_le_iff₀ hl).mp
  exact hc.trans (by simp [matrixMomentOrder])

theorem geometric_dimension_bound {d : ℕ} (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ)
    {k : ℕ} (hk : Real.log ((d:ℝ)/δ) ≤ (k:ℝ)*Real.log 2) :
    (d:ℝ)*(1/2:ℝ)^k ≤ δ := by
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have he : (1/2:ℝ)^k = Real.exp (-(k:ℝ)*Real.log 2) := by
    rw [show (1/2:ℝ) = Real.exp (-Real.log 2) by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)]; norm_num]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  calc
    _ ≤ (d:ℝ)*Real.exp (-Real.log ((d:ℝ)/δ)) := by
      apply mul_le_mul_of_nonneg_left _ hd'.le
      apply Real.exp_le_exp.mpr
      linarith
    _ = δ := by
      rw [Real.exp_neg, Real.exp_log (div_pos hd' hδ)]
      field_simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A genuine operator-norm confidence bound with logarithmic dimension and
confidence dependence. The sample requirement has no added dimension term;
the small-radius case is proved deterministically. -/
theorem independent_operator_average_confidence {n : ℕ}
    (X : Fin n → Ω → (E →L[ℝ] E)) (hX : ∀ i, Measurable (X i))
    {σ η δ : ℝ} (hσ : 0 ≤ σ) (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n)
    (hb : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ σ)
    (hind : iIndepFun X μ) (hzero : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsym : ∀ i, ∀ᵐ ω ∂μ, (X i ω).toLinearMap.IsSymmetric)
    (hsize : 8*(matrixMomentOrder (Module.finrank ℝ E + 1) δ : ℝ)*σ^2 ≤
      (n:ℝ)*η^2) :
    μ.real {ω | η ≤ ‖(n:ℝ)⁻¹ • ∑ i, X i ω‖} ≤ δ := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  by_cases hsmall : σ < η
  · have hall : ∀ᵐ ω ∂μ, ∀ i, ‖X i ω‖ ≤ σ := ae_all_iff.mpr hb
    have havg : ∀ᵐ ω ∂μ, ‖(n:ℝ)⁻¹ • ∑ i, X i ω‖ ≤ σ := by
      filter_upwards [hall] with ω hω
      rw [norm_smul (n:ℝ)⁻¹ (∑ i, X i ω), Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn'), inv_mul_eq_div]
      apply (div_le_iff₀ hn').mpr
      calc
        _ ≤ ∑ i, ‖X i ω‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin n, σ := Finset.sum_le_sum (fun i _ => hω i)
        _ = _ := by simp [mul_comm]
    have hz : μ {ω | η ≤ ‖(n:ℝ)⁻¹ • ∑ i, X i ω‖} = 0 := by
      apply measure_zero_iff_ae_nmem.mpr
      filter_upwards [havg] with ω hω
      exact not_le_of_gt (lt_of_le_of_lt hω hsmall)
    simpa only [measureReal_def, hz, ENNReal.toReal_zero] using hδ.le
  · let k := matrixMomentOrder (Module.finrank ℝ E + 1) δ
    have hk : 0 < k := matrixMomentOrder_pos _ _
    have hs : η ≤ σ := le_of_not_gt hsmall
    have hsq : η^2 ≤ σ^2 := pow_le_pow_left₀ hη.le hs 2
    have hmul := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    have hknR : (k:ℝ) ≤ (n:ℝ) := by
      apply (mul_le_mul_right (sq_pos_of_pos hη)).mp
      have hks : 0 ≤ (k:ℝ)*σ^2 := by positivity
      change 8*(k:ℝ)*σ^2 ≤ (n:ℝ)*η^2 at hsize
      nlinarith
    have hkn : k ≤ n := by exact_mod_cast hknR
    have hratio : 4*(k:ℝ)*σ^2/((n:ℝ)*η^2) ≤ (1/2:ℝ) := by
      apply (div_le_iff₀ (mul_pos hn' (sq_pos_of_pos hη))).mpr
      change 8*(k:ℝ)*σ^2 ≤ (n:ℝ)*η^2 at hsize
      nlinarith
    calc
      _ ≤ (Module.finrank ℝ E : ℝ)*(4*(k:ℝ)*σ^2/((n:ℝ)*η^2))^k :=
        independent_operator_average_tail X hX hσ hb hind hzero hsym hk hkn hη
      _ ≤ (Module.finrank ℝ E : ℝ)*(1/2:ℝ)^k := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact pow_le_pow_left₀ (by positivity) hratio _
      _ ≤ (Module.finrank ℝ E + 1 : ℕ)*(1/2:ℝ)^k := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.le_succ (Module.finrank ℝ E)
      _ ≤ δ := geometric_dimension_bound (Nat.succ_pos _) hδ (matrixMomentOrder_log _ _)

end
end SampleReuse
