import FreshGradientMinimax.HistoryKL
import FreshGradientMinimax.TestingOracleKL
import FreshGradientMinimax.TestingZeroQuery
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Theorem D.1: the actual clipped hard pair and Gaussian fresh oracle
force the stated statistical number of original calls for every unrestricted
adaptive randomized algorithm. The numerical constant matches the paper. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

theorem disjoint_success_event_bound {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {E F : Set Ω}
    (hF : MeasurableSet F) (hd : Disjoint E F) (hs : 2 / 3 ≤ ν.real F) :
    ν.real E ≤ 1 / 3 := by
  have hu := measureReal_union (μ := ν) hd hF
  have hm : ν.real (E ∪ F) ≤ 1 := by
    simpa only [measureReal_univ_eq_one] using
      measureReal_mono (μ := ν) (Set.subset_univ (E ∪ F))
  linarith

theorem testing_pair_lower (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (A : RandomizedAlgorithm 1 1) (N : ℕ)
    (hF : 2 / 3 ≤ (A.outputLaw
      (FreshOracle.gaussianDual (testingHardObjective p hκ 1 (by norm_num)) p.σ).kernel N).real
      ((testingHardObjective p hκ 1 (by norm_num)).successSet p.ε))
    (hH : 2 / 3 ≤ (A.outputLaw
      (FreshOracle.gaussianDual (testingHardObjective p hκ (-1) (by norm_num)) p.σ).kernel N).real
      ((testingHardObjective p hκ (-1) (by norm_num)).successSet p.ε)) :
    (2 / (9 * 903168) : ℝ) * p.testing ≤ N := by
  by_cases hσ : p.σ = 0
  · simp only [Parameters.testing, hσ, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, zero_div]
    exact Nat.cast_nonneg N
  have hσp : 0 < p.σ := lt_of_le_of_ne p.σ_nonneg (Ne.symm hσ)
  have hκp : 0 < p.κ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) p.condition_ge_one
  have he := disjoint_success_event_bound
    ((testingHardObjective p hκ (-1) (by norm_num)).successSet_measurable p.ε)
    (testingHardObjective_success_disjoint p hκ) hH
  have hc : 0 ≤ 903168 * p.ε ^ 2 / (p.κ ^ 2 * p.σ ^ 2) := by positivity
  have ht := A.policy.output_testing_information A.seedLaw hc
    (testingOracle_one_query_kl p hκ hσp)
    ((testingHardObjective p hκ 1 (by norm_num)).successSet_measurable p.ε) N hF he
  have hlog : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at h
    exact h
  have ht' : (2 : ℝ) / 9 ≤ (N : ℝ) * (903168 * p.ε ^ 2 / (p.κ ^ 2 * p.σ ^ 2)) := by
    linarith
  rw [← mul_div_assoc] at ht'
  have hm := (le_div_iff₀ (by positivity : 0 < p.κ ^ 2 * p.σ ^ 2)).mp ht'
  unfold Parameters.testing
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos p.ε_pos)).mpr
  nlinarith only [hm]

theorem testing_pair_positive (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (A : RandomizedAlgorithm 1 1) (N : ℕ)
    (hF : 2 / 3 ≤ (A.outputLaw
      (FreshOracle.gaussianDual (testingHardObjective p hκ 1 (by norm_num)) p.σ).kernel N).real
      ((testingHardObjective p hκ 1 (by norm_num)).successSet p.ε))
    (hH : 2 / 3 ≤ (A.outputLaw
      (FreshOracle.gaussianDual (testingHardObjective p hκ (-1) (by norm_num)) p.σ).kernel N).real
      ((testingHardObjective p hκ (-1) (by norm_num)).successSet p.ε)) : 1 ≤ N := by
  apply Nat.one_le_iff_ne_zero.mpr
  rintro rfl
  have he := A.policy.zero_query_law_independent A.seedLaw
    (FreshOracle.gaussianDual (testingHardObjective p hκ 1 (by norm_num)) p.σ).kernel
    (FreshOracle.gaussianDual (testingHardObjective p hκ (-1) (by norm_num)) p.σ).kernel
  change A.outputLaw _ 0 = A.outputLaw _ 0 at he
  rw [← he] at hH
  exact disjoint_testing_obstruction _ _
    ((testingHardObjective p hκ (-1) (by norm_num)).successSet_measurable p.ε)
    (testingHardObjective_success_disjoint p hκ) ⟨hF, hH⟩

theorem testing_localized_budget_lower (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (hgap : 151424 * p.μ * p.ε ^ 2 / p.L ^ 2 ≤ p.gap)
    {N : ℕ} (hN : BudgetSuffices p (some p.G) N) :
    (2 / (9 * 903168) : ℝ) * p.testing ≤ N := by
  obtain ⟨A, hA⟩ := hN 1 1
  exact testing_pair_lower p hκ A N
    (hA _ (FreshOracle.gaussianDual _ p.σ) (testingHardObjective_inClass p hκ hgap 1 (by norm_num)))
    (hA _ (FreshOracle.gaussianDual _ p.σ) (testingHardObjective_inClass p hκ hgap (-1) (by norm_num)))

theorem testing_unlocalized_budget_lower (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (hgap : 151424 * p.μ * p.ε ^ 2 / p.L ^ 2 ≤ p.gap)
    {N : ℕ} (hN : BudgetSuffices p none N) :
    (2 / (9 * 903168) : ℝ) * p.testing ≤ N :=
  testing_localized_budget_lower p hκ hgap (localized_budget_of_unlocalized hN p.G)

end FreshGradientMinimax
