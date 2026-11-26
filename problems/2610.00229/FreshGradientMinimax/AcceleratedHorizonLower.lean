import FreshGradientMinimax.AcceleratedLabelDistribution
import FreshGradientMinimax.AcceleratedPhysicalFamily

/-! The actual minimax budget cannot fit inside the accelerated hiding
horizon. The exact oracle belongs to every larger noise budget. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem accelerated_horizon_impossible (p : Parameters) (n k H : ℕ) (hn : 10 ≤ n + 2) (hk : 0 < k)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ p.L / (4 * acceleratedSmoothnessConstant * p.μ))
    (hgap : 1000 * (k + 1 : ℕ) * acceleratedValueScale p.L p.ε ≤ p.gap)
    (hH : 2 * H + 2 ≤ acceleratedStageCount n k) : ¬ BudgetSuffices p (some p.G) H := by
  intro hbudget
  have hL := p.μ_pos.trans_le p.μ_le_L
  obtain ⟨A, hA⟩ := hbudget (acceleratedLabelDimension n k H) (acceleratedLabelDimension n k H)
  have hu := accelerated_finite_label_success_bound n k H hn hk hL p.ε_pos p.μ_pos hchain p.σ hH A.policy A.seedLaw
  have hl : (2 / 3 : ℝ) ≤
      (𝔼 z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin (acceleratedLabelDimension n k H),
        (A.policy.outputLaw A.seedLaw (FreshOracle.exact
          (acceleratedPhysicalModel (acceleratedPrimalLabelFrame (acceleratedLabelDimension_size n k H) z)
            (acceleratedDualLabelFrame (acceleratedLabelDimension_size n k H) z) hn hk hL p.ε_pos p.μ_pos hchain) p.σ).kernel H).real
          ((acceleratedPhysicalModel (acceleratedPrimalLabelFrame (acceleratedLabelDimension_size n k H) z)
            (acceleratedDualLabelFrame (acceleratedLabelDimension_size n k H) z) hn hk hL p.ε_pos p.μ_pos hchain).successSet p.ε)) := by
    apply Finset.le_expect Finset.univ_nonempty
    intro z _
    apply hA
    exact acceleratedPhysicalModel_in_class p _ _ hn hk hchain hgap
  linarith only [hl, hu]

theorem accelerated_budget_strict (p : Parameters) (n k : ℕ) (hn : 10 ≤ n + 2) (hk : 0 < k)
    (hchain : (n + 2 : ℝ) ^ 2 ≤ p.L / (4 * acceleratedSmoothnessConstant * p.μ))
    (hgap : 1000 * (k + 1 : ℕ) * acceleratedValueScale p.L p.ε ≤ p.gap)
    {H : ℕ} (hH : BudgetSuffices p (some p.G) H) :
    ((acceleratedStageCount n k : ℝ) - 2) / 2 < H := by
  apply lt_of_not_ge
  intro h
  have hh : (2 : ℝ) * H + 2 ≤ acceleratedStageCount n k := by linarith only [h]
  have hh' : 2 * H + 2 ≤ acceleratedStageCount n k := by exact_mod_cast hh
  exact accelerated_horizon_impossible p n k H hn hk hchain hgap hh' hH

end FreshGradientMinimax
