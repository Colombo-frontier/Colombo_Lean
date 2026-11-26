import FreshGradientMinimax.PrimalLabelDistribution
import FreshGradientMinimax.PrimalProtectionLemma

/-! The finite hard distribution rules out the paper's full progress horizon
in the actual minimax definition, with zero initial dual localization. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem primal_horizon_impossible (p : Parameters) (n N : ℕ) (hn : 0 < n)
    (hm : p.μ ≤ p.L / (4 * primalScalingConstant))
    (hgap : 18 * (n + 1 : ℝ) * primalValueScale p.L p.ε ≤ p.gap)
    (hN : (N : ℝ) ≤ (n : ℝ) / (12 * primalRevealProbability p.L p.ε p.μ p.σ)) :
    ¬ BudgetSuffices p (some p.G) N := by
  intro hbudget
  have hL := p.μ_pos.trans_le p.μ_le_L
  obtain ⟨A, hA⟩ := hbudget (primalLabelDimension n N p.L p.ε p.μ) (primalLabelDimension n N p.L p.ε p.μ)
  have hu := primal_finite_label_success_bound n N hn hL p.ε_pos p.μ_pos hm p.σ hN A.policy A.seedLaw
  have hl : (2 / 3 : ℝ) ≤
      (𝔼 z : Fin ((n + 1) + (n + n)) → Fin (primalLabelDimension n N p.L p.ε p.μ),
        (A.policy.outputLaw A.seedLaw (primalFreshOracle (primalLabelFrame (primalLabelDimension_size n N p.L p.ε p.μ) z)
          (dualLabelFrame (primalLabelDimension_size n N p.L p.ε p.μ) z) hL p.ε_pos p.μ_pos hm p.σ).kernel N).real
          ((paperCompressedModel (primalLabelFrame (primalLabelDimension_size n N p.L p.ε p.μ) z)
            (dualLabelFrame (primalLabelDimension_size n N p.L p.ε p.μ) z) hL p.ε_pos p.μ_pos hm).successSet p.ε)) := by
    apply Finset.le_expect Finset.univ_nonempty
    intro z _
    apply hA
    refine ⟨paperCompressedModel_gap _ _ hL p.ε_pos p.μ_pos hm hgap, ?_⟩
    exact (paperCompressedModel_localized_zero _ _ hL p.ε_pos p.μ_pos hm).trans p.G_nonneg
  linarith

theorem primal_budget_strict (p : Parameters) (n : ℕ) (hn : 0 < n)
    (hm : p.μ ≤ p.L / (4 * primalScalingConstant))
    (hgap : 18 * (n + 1 : ℝ) * primalValueScale p.L p.ε ≤ p.gap)
    {N : ℕ} (hN : BudgetSuffices p (some p.G) N) :
    (n : ℝ) / (12 * primalRevealProbability p.L p.ε p.μ p.σ) < N := by
  apply lt_of_not_ge
  intro hle
  exact primal_horizon_impossible p n N hn hm hgap hle hN

theorem primal_floor_budget_strict (p : Parameters) (n : ℕ) (hn : 0 < n)
    (hκ : 4 * primalScalingConstant ≤ p.κ)
    (hfloor : n + 1 = ⌊p.gap / (32 * primalValueScale p.L p.ε)⌋₊)
    {N : ℕ} (hN : BudgetSuffices p (some p.G) N) :
    (n : ℝ) / (12 * primalRevealProbability p.L p.ε p.μ p.σ) < N :=
  primal_budget_strict p n hn (primal_mu_bound_of_condition p.μ_pos hκ)
    (primal_floor_gap (primalValueScale_pos (p.μ_pos.trans_le p.μ_le_L) p.ε_pos) p.gap_nonneg hfloor) hN

theorem primal_horizon_complexity (p : Parameters) (n : ℕ) (hn : 0 < n)
    (hm : p.μ ≤ p.L / (4 * primalScalingConstant))
    (hgap : 18 * (n + 1 : ℝ) * primalValueScale p.L p.ε ≤ p.gap) :
    (⌈(n : ℝ) / (12 * primalRevealProbability p.L p.ε p.μ p.σ)⌉₊ : ℕ∞) ≤ localizedComplexity p := by
  unfold localizedComplexity oracleComplexity
  apply le_iInf
  intro N
  exact_mod_cast Nat.ceil_le.mpr (primal_budget_strict p n hn hm hgap N.property).le

end FreshGradientMinimax
