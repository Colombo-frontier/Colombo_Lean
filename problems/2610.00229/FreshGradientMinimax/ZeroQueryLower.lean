import FreshGradientMinimax.QuadraticWitness
import FreshGradientMinimax.Probability

/-! A genuine zero-query obstruction in the localized oracle model.
Two translated quadratics suffice in the stated gap regime. This closes
the integer endpoint but makes no positive-budget statistical claim. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def zeroQueryCenter (L ε : ℝ) : Euclid 1 := EuclideanSpace.single (0 : Fin 1) (2 * ε / L)

theorem zeroQueryCenter_norm {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    ‖zeroQueryCenter L ε‖ = 2 * ε / L := by
  rw [zeroQueryCenter, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem zero_query_not_sufficient (p : Parameters) (hgap : 2 * p.ε ^ 2 / p.L ≤ p.gap) :
    ¬ BudgetSuffices p (some p.G) 0 := by
  intro hbudget
  have hL : 0 < p.L := p.μ_pos.trans_le p.μ_le_L
  let c := zeroQueryCenter p.L p.ε
  let F := quadraticWitness 1 1 p.L p.μ p.μ_pos p.μ_le_L c
  let H := quadraticWitness 1 1 p.L p.μ p.μ_pos p.μ_le_L (-c)
  have hc : ‖c‖ = 2 * p.ε / p.L := zeroQueryCenter_norm hL p.ε_pos
  have hclass (d : Euclid 1) (hd : ‖d‖ = 2 * p.ε / p.L) :
      InLocalizedClass (quadraticWitness 1 1 p.L p.μ p.μ_pos p.μ_le_L d) p.gap (some p.G) := by
    refine ⟨?_, quadraticWitness_localized p.μ_pos p.μ_le_L d p.G_nonneg⟩
    have he : p.L / 2 * ‖d‖ ^ 2 = 2 * p.ε ^ 2 / p.L := by
      rw [hd]
      field_simp [ne_of_gt hL]
      ring
    intro x
    have hg := quadraticWitness_gap (dy := 1) p.μ_pos p.μ_le_L d x
    rw [he] at hg
    exact hg.trans hgap
  have hsep : 2 * p.ε < p.L * ‖c - -c‖ := by
    have hn : ‖c - -c‖ = 2 * ‖c‖ := by
      rw [sub_neg_eq_add, ← two_smul ℝ c, norm_smul]
      norm_num
    rw [hn, hc]
    have he : p.L * (2 * (2 * p.ε / p.L)) = 4 * p.ε := by field_simp [ne_of_gt hL]; ring
    rw [he]
    linarith [p.ε_pos]
  have hdis : Disjoint (F.successSet p.ε) (H.successSet p.ε) :=
    quadraticWitness_success_disjoint p.μ_pos p.μ_le_L c (-c) hsep
  obtain ⟨A, hA⟩ := hbudget 1 1
  have hF := hA F (FreshOracle.exact F p.σ) (hclass c hc)
  have hH := hA H (FreshOracle.exact H p.σ) (hclass (-c) (by rw [norm_neg, hc]))
  have he : A.outputLaw (FreshOracle.exact F p.σ).kernel 0 =
      A.outputLaw (FreshOracle.exact H p.σ).kernel 0 :=
    A.policy.zero_query_law_independent A.seedLaw _ _
  rw [← he] at hH
  exact disjoint_testing_obstruction (ν := A.outputLaw (FreshOracle.exact F p.σ).kernel 0)
    (F.successSet p.ε) (H.successSet p.ε) (H.successSet_measurable p.ε) hdis ⟨hF, hH⟩

theorem localized_budget_positive (p : Parameters) (hgap : 2 * p.ε ^ 2 / p.L ≤ p.gap)
    {N : ℕ} (hN : BudgetSuffices p (some p.G) N) : 1 ≤ N := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro he
  rw [he] at hN
  exact zero_query_not_sufficient p hgap hN

theorem unlocalized_budget_positive (p : Parameters) (hgap : 2 * p.ε ^ 2 / p.L ≤ p.gap)
    {N : ℕ} (hN : BudgetSuffices p none N) : 1 ≤ N :=
  localized_budget_positive p hgap (localized_budget_of_unlocalized hN p.G)

theorem localized_complexity_one_le (p : Parameters) (hgap : 2 * p.ε ^ 2 / p.L ≤ p.gap) :
    1 ≤ localizedComplexity p := by
  unfold localizedComplexity oracleComplexity
  apply le_iInf
  intro N
  exact_mod_cast localized_budget_positive p hgap N.property

theorem unlocalized_complexity_one_le (p : Parameters) (hgap : 2 * p.ε ^ 2 / p.L ≤ p.gap) :
    1 ≤ unlocalizedComplexity p :=
  (localized_complexity_one_le p hgap).trans (localized_complexity_le_unlocalized p)

end FreshGradientMinimax
