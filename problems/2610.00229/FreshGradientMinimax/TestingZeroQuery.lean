import FreshGradientMinimax.TestingFamily
import FreshGradientMinimax.Probability

/-! The zero-query endpoint using the actual localized clipped family. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

theorem testing_zero_query_not_sufficient (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (hgap : 151424 * p.μ * p.ε ^ 2 / p.L ^ 2 ≤ p.gap) :
    ¬ BudgetSuffices p (some p.G) 0 := by
  intro hbudget
  let F := testingHardObjective p hκ 1 (by norm_num)
  let H := testingHardObjective p hκ (-1) (by norm_num)
  obtain ⟨A, hA⟩ := hbudget 1 1
  have hF := hA F (FreshOracle.exact F p.σ) (testingHardObjective_inClass p hκ hgap 1 (by norm_num))
  have hH := hA H (FreshOracle.exact H p.σ) (testingHardObjective_inClass p hκ hgap (-1) (by norm_num))
  have he : A.outputLaw (FreshOracle.exact F p.σ).kernel 0 =
      A.outputLaw (FreshOracle.exact H p.σ).kernel 0 :=
    A.policy.zero_query_law_independent A.seedLaw _ _
  rw [← he] at hH
  exact disjoint_testing_obstruction (ν := A.outputLaw (FreshOracle.exact F p.σ).kernel 0)
    (F.successSet p.ε) (H.successSet p.ε) (H.successSet_measurable p.ε)
    (testingHardObjective_success_disjoint p hκ) ⟨hF, hH⟩

theorem testing_localized_budget_positive (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (hgap : 151424 * p.μ * p.ε ^ 2 / p.L ^ 2 ≤ p.gap)
    {N : ℕ} (hN : BudgetSuffices p (some p.G) N) : 1 ≤ N := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro he
  rw [he] at hN
  exact testing_zero_query_not_sufficient p hκ hgap hN

theorem testing_localized_complexity_one_le (p : Parameters) (hκ : 1120 * p.μ ≤ p.L)
    (hgap : 151424 * p.μ * p.ε ^ 2 / p.L ^ 2 ≤ p.gap) : 1 ≤ localizedComplexity p := by
  unfold localizedComplexity oracleComplexity
  apply le_iInf
  intro N
  exact_mod_cast testing_localized_budget_positive p hκ hgap N.property

end FreshGradientMinimax
