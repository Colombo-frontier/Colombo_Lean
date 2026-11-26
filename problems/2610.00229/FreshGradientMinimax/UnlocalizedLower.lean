import FreshGradientMinimax.LabelDistribution
import FreshGradientMinimax.MainStatements

/-! The complete infinite-complexity assertion of Theorem 3.6. Every finite
query horizon is defeated by an explicit finite distribution of actual globally
smooth, strongly concave objectives with exact fresh oracles. The same family
also excludes a localized horizon whenever its calibrated signal fits G. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem label_distribution_obstruction (p : Parameters) (hκ : 4 * p.μ ≤ p.L) (N : ℕ)
    (A : RandomizedAlgorithm 1 (labelHidingDimension p N))
    (h : ∀ (z : Fin (4 * N + 4) → Fin (labelHidingDimension p N)) (s : ℝ) (hs : s ^ 2 = 1),
      2 / 3 ≤ (A.outputLaw (FreshOracle.exact
        (pathHorizonObjective p hκ N (labelFrame (labelHidingDimension_size p N) z) s hs) p.σ).kernel N).real
          ((pathHorizonObjective p hκ N (labelFrame (labelHidingDimension_size p N) z) s hs).successSet p.ε)) :
    False := by
  have hl : (2 / 3 : ℝ) ≤ labelAverageSuccess p hκ N A := by
    unfold labelAverageSuccess
    apply Finset.le_expect Finset.univ_nonempty
    intro z _
    have hp := h z 1 (by norm_num)
    have hn := h z (-1) (by norm_num)
    linarith
  have hu := label_distribution_success_bound p hκ N A
  linarith

theorem localized_label_horizon_impossible (p : Parameters) (hκ : 4 * p.μ ≤ p.L)
    (hgap : 80 * p.ε ^ 2 / p.L ≤ p.gap) (N : ℕ)
    (hG : pathHardSignal p.L p.μ p.ε (4 * N + 3) ≤ p.G) :
    ¬ BudgetSuffices p (some p.G) N := by
  intro hN
  obtain ⟨A, hA⟩ := hN 1 (labelHidingDimension p N)
  apply label_distribution_obstruction p hκ N A
  intro z s hs
  exact hA _ _ (pathHorizonObjective_inClass p hκ N hgap hG _ s hs)

theorem unlocalized_label_horizon_impossible (p : Parameters) (hκ : 4 * p.μ ≤ p.L)
    (hgap : 80 * p.ε ^ 2 / p.L ≤ p.gap) (N : ℕ) : ¬ BudgetSuffices p none N := by
  intro hN
  obtain ⟨A, hA⟩ := hN 1 (labelHidingDimension p N)
  apply label_distribution_obstruction p hκ N A
  intro z s hs
  exact hA _ _ (pathHorizonObjective_unlocalized p hκ N hgap _ s hs)

theorem theorem_36 (p : Parameters) (hκ : 4 * p.μ ≤ p.L)
    (hgap : 80 * p.ε ^ 2 / p.L ≤ p.gap) : unlocalizedComplexity p = ⊤ :=
  (complexity_eq_top_iff p none).mpr (unlocalized_label_horizon_impossible p hκ hgap)

theorem main_theorem_36_statement : MainTheorem36Statement := theorem_36

theorem theorem_36_fixed_distribution (p : Parameters) (hκ : 4 * p.μ ≤ p.L)
    (hgap : 80 * p.ε ^ 2 / p.L ≤ p.gap) (N : ℕ) :
    (∀ (z : Fin (4 * N + 4) → Fin (labelHidingDimension p N)) (s : ℝ) (hs : s ^ 2 = 1),
      (pathHorizonObjective p hκ N (labelFrame (labelHidingDimension_size p N) z) s hs).PrimalGapAtMost p.gap) ∧
    (∀ A : RandomizedAlgorithm 1 (labelHidingDimension p N), labelAverageSuccess p hκ N A < (2 / 3 : ℝ)) := by
  constructor
  · intro z s hs x
    exact (pathHorizonObjective_gap p hκ N _ s hs x).trans hgap
  · intro A
    exact (label_distribution_success_bound p hκ N A).trans_lt (by norm_num)

end FreshGradientMinimax
