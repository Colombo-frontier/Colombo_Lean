import FreshGradientMinimax.AcceleratedHorizonLower

/-! Theorem E.3 with universal constants, integer budgets, arbitrary
measurable randomized algorithms, and arbitrary localization/noise budgets. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def acceleratedLowerCoefficient : ℝ := acceleratedStageCoefficient / 4

theorem acceleratedLowerCoefficient_pos : 0 < acceleratedLowerCoefficient :=
  div_pos acceleratedStageCoefficient_pos (by norm_num)

theorem accelerated_budget_lower (p : Parameters)
    (hκ : acceleratedConditionThreshold ≤ p.κ)
    (hgap : acceleratedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap)
    {H : ℕ} (hH : BudgetSuffices p (some p.G) H) :
    acceleratedLowerCoefficient * p.deterministic ≤ H := by
  obtain ⟨n, k, hn, hk, _, _, hchain, hgap', hsize⟩ := accelerated_physical_parameters p hκ hgap
  exact hsize.trans (accelerated_budget_strict p n k hn hk hchain hgap' hH).le

theorem accelerated_complexity_lower (p : Parameters)
    (hκ : acceleratedConditionThreshold ≤ p.κ)
    (hgap : acceleratedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap) :
    (⌈acceleratedLowerCoefficient * p.deterministic⌉₊ : ℕ∞) ≤ localizedComplexity p := by
  unfold localizedComplexity oracleComplexity
  apply le_iInf
  intro H
  exact_mod_cast Nat.ceil_le.mpr (accelerated_budget_lower p hκ hgap H.property)

theorem accelerated_lower_statement :
    ∃ c C₀ κ₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ 0 < κ₀ ∧
      ∀ p : Parameters, κ₀ ≤ p.κ → C₀ * p.ε ^ 2 ≤ p.L * p.gap →
        ∀ H : ℕ, BudgetSuffices p (some p.G) H → c * p.deterministic ≤ H := by
  exact ⟨acceleratedLowerCoefficient, acceleratedGapThreshold, acceleratedConditionThreshold,
    acceleratedLowerCoefficient_pos, acceleratedGapThreshold_pos, acceleratedConditionThreshold_pos,
    fun p hκ hgap _ hH => accelerated_budget_lower p hκ hgap hH⟩

theorem theorem_E3 :
    ∃ c C₀ κ₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ 0 < κ₀ ∧
      ∀ p : Parameters, κ₀ ≤ p.κ → C₀ * p.ε ^ 2 ≤ p.L * p.gap →
        (⌈c * p.deterministic⌉₊ : ℕ∞) ≤ localizedComplexity p := by
  exact ⟨acceleratedLowerCoefficient, acceleratedGapThreshold, acceleratedConditionThreshold,
    acceleratedLowerCoefficient_pos, acceleratedGapThreshold_pos, acceleratedConditionThreshold_pos,
    fun p hκ hgap => accelerated_complexity_lower p hκ hgap⟩

end FreshGradientMinimax
