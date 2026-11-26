import SampleReuse.OperatorSumMoment

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SampleReuse
noncomputable section
open Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} (X : Fin n → Ω → (E →L[ℝ] E)) (hX : ∀ i, Measurable (X i))
  {σ : ℝ} (hσ : 0 ≤ σ) (hb : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ σ)
  (hind : iIndepFun X μ) (hzero : ∀ i, (∫ ω, X i ω ∂μ) = 0)
  (hsym : ∀ i, ∀ᵐ ω ∂μ, (X i ω).toLinearMap.IsSymmetric)

include hX hσ hb hind hzero hsym

theorem independent_operator_sum_tail {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ‖∑ i, X i ω‖} ≤
      (Module.finrank ℝ E : ℝ)*(4*(k:ℝ)*(n:ℝ)*σ^2)^k / t^(2*k) := by
  have hsub : {ω | t ≤ ‖∑ i, X i ω‖} ⊆
      {ω | t^(2*k) ≤ ‖∑ i, X i ω‖^(2*k)} := by
    intro ω hω
    exact pow_le_pow_left₀ ht.le hω _
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => pow_nonneg (norm_nonneg (∑ i, X i ω)) (2*k)))
    (operator_sum_norm_even_integrable X hX hσ hb hsym hk) (t^(2*k))
  have hbnd := independent_operator_norm_even_moment X hX hσ hb hind hzero hsym hk hkn
  apply (le_div_iff₀ (pow_pos ht _)).mpr
  calc
    _ ≤ μ.real {ω | t^(2*k) ≤ ‖∑ i, X i ω‖^(2*k)} * t^(2*k) :=
      mul_le_mul_of_nonneg_right (measureReal_mono hsub) (pow_nonneg ht.le _)
    _ ≤ ∫ ω, ‖∑ i, X i ω‖^(2*k) ∂μ := by simpa [mul_comm] using hm
    _ ≤ _ := hbnd

/-- A dimension-linear probability prefactor yields a logarithmic-dimension
sample size by choosing the even moment order proportional to log(d/δ). -/
theorem independent_operator_average_tail {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {η : ℝ} (hη : 0 < η) :
    μ.real {ω | η ≤ ‖(n:ℝ)⁻¹ • ∑ i, X i ω‖} ≤
      (Module.finrank ℝ E : ℝ)*(4*(k:ℝ)*σ^2/((n:ℝ)*η^2))^k := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le hk hkn)
  have hsub : {ω | η ≤ ‖(n:ℝ)⁻¹ • ∑ i, X i ω‖} ⊆
      {ω | (n:ℝ)*η ≤ ‖∑ i, X i ω‖} := by
    intro ω hω
    change η ≤ ‖(n:ℝ)⁻¹ • ∑ i, X i ω‖ at hω
    rw [norm_smul (n:ℝ)⁻¹ (∑ i, X i ω)] at hω
    simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_eq_div] at hω
    simpa [mul_comm] using (le_div_iff₀ hn).mp hω
  have h := independent_operator_sum_tail X hX hσ hb hind hzero hsym hk hkn (mul_pos hn hη)
  have he : (4*(k:ℝ)*(n:ℝ)*σ^2)/((n:ℝ)*η)^2 =
      4*(k:ℝ)*σ^2/((n:ℝ)*η^2) := by
    field_simp
    ring
  calc
    _ ≤ μ.real {ω | (n:ℝ)*η ≤ ‖∑ i, X i ω‖} := measureReal_mono hsub
    _ ≤ _ := h
    _ = (Module.finrank ℝ E : ℝ) *
        ((4*(k:ℝ)*(n:ℝ)*σ^2)/((n:ℝ)*η)^2)^k := by
      rw [div_pow, pow_mul]
      ring
    _ = _ := by rw [he]

end
end SampleReuse
