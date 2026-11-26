import Mathlib

open MeasureTheory

namespace Task006.LowerEventMass

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The posterior-conditioning event has mass at least one half, derived from
the paid-access expectation and pathwise rank ledger. -/
theorem rank_lt_threshold_half_mass (K rank : Ω → ℝ) (d k : ℝ)
    (hK : Integrable K μ) (hK0 : ∀ ω, 0 ≤ K ω) (hr : Measurable rank)
    (hk : 0 < k) (hdk : d ≤ 8*k)
    (hEK : (∫ ω, K ω ∂μ) ≤ d/32)
    (hledger : ∀ ω, rank ω ≤ 2*K ω) :
    (1/2 : ℝ) ≤ μ.real {ω | rank ω < k} := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hK0) hK (k/2)
  have hbad : μ.real {ω | k/2 ≤ K ω} ≤ 1/2 := by
    nlinarith
  have hsub : {ω | k ≤ rank ω} ⊆ {ω | k/2 ≤ K ω} := by
    intro ω hω
    have h := hledger ω
    dsimp only [Set.mem_setOf_eq] at hω ⊢
    linarith
  have hbad' := (measureReal_mono (μ := μ) hsub).trans hbad
  have he : {ω | rank ω < k} = {ω | k ≤ rank ω}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq,Set.mem_compl_iff,not_le]
  rw [he,probReal_compl_eq_one_sub (measurableSet_le measurable_const hr)]
  linarith

theorem rank_zero_small_dimension_mass (K rank : Ω → ℕ)
    (hK : Integrable (fun ω => (K ω : ℝ)) μ) (hr : Measurable rank)
    (hEK : (∫ ω, (K ω : ℝ) ∂μ) ≤ 7/32)
    (hledger : ∀ ω, rank ω ≤ 2*K ω) :
    (25/32 : ℝ) ≤ μ.real {ω | rank ω = 0} := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg (K ω))) hK (1 : ℝ)
  have hsub : {ω | rank ω ≠ 0} ⊆ {ω | (1 : ℝ) ≤ (K ω : ℝ)} := by
    intro ω hω
    have h := hledger ω
    have hKn : 1 ≤ K ω := by
      change rank ω ≠ 0 at hω
      omega
    exact_mod_cast hKn
  have hb := measureReal_mono (μ := μ) hsub
  have he : {ω | rank ω = 0} = {ω | rank ω ≠ 0}ᶜ := by ext ω; simp
  have hs : MeasurableSet {ω | rank ω ≠ 0} := (hr (measurableSet_singleton 0)).compl
  rw [he,probReal_compl_eq_one_sub hs]
  simp only [one_mul] at hmarkov
  linarith

end Task006.LowerEventMass
