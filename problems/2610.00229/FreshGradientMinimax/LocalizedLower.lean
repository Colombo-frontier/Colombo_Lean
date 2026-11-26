import FreshGradientMinimax.AcceleratedLowerRate
import FreshGradientMinimax.PrimalLowerRate
import FreshGradientMinimax.TestingMinimax
import FreshGradientMinimax.LocalizationLower
import FreshGradientMinimax.OuterRateParameters

/-! The four actual minimax lower bounds imply the complete localized
rate. All constants are universal and precede the problem parameters. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def localizedLowerBase : ℝ := min acceleratedLowerCoefficient
  (min primalLowerCoefficient (min (2 / (9 * 903168)) (1 / 1024)))
def localizedLowerCoefficient : ℝ := localizedLowerBase / 4
def localizedGapThreshold : ℝ := max (max acceleratedGapThreshold primalGapThreshold) 80
def localizedConditionThreshold : ℝ := max (max acceleratedConditionThreshold (4 * primalScalingConstant)) 8192

theorem localizedLowerBase_pos : 0 < localizedLowerBase :=
  lt_min acceleratedLowerCoefficient_pos (lt_min primalLowerCoefficient_pos (by norm_num))

theorem localizedLowerCoefficient_pos : 0 < localizedLowerCoefficient := div_pos localizedLowerBase_pos (by norm_num)

theorem localizedGapThreshold_pos : 0 < localizedGapThreshold :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 80) (le_max_right _ _)

theorem localizedConditionThreshold_pos : 0 < localizedConditionThreshold :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8192) (le_max_right _ _)

theorem localizedLowerBase_bounds :
    localizedLowerBase ≤ acceleratedLowerCoefficient ∧ localizedLowerBase ≤ primalLowerCoefficient ∧
    localizedLowerBase ≤ 2 / (9 * 903168) ∧ localizedLowerBase ≤ 1 / 1024 := by
  exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _),
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)⟩

theorem localized_budget_lower (p : Parameters) (hκ : localizedConditionThreshold ≤ p.κ)
    (hgap : localizedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap)
    {N : ℕ} (hN : BudgetSuffices p (some p.G) N) : localizedLowerCoefficient * p.rate ≤ N := by
  have hκA : acceleratedConditionThreshold ≤ p.κ := ((le_max_left _ _).trans (le_max_left _ _)).trans hκ
  have hκB : 4 * primalScalingConstant ≤ p.κ := ((le_max_right _ _).trans (le_max_left _ _)).trans hκ
  have hκC : 8192 ≤ p.κ := (le_max_right _ _).trans hκ
  have hgA : acceleratedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap :=
    (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (sq_nonneg _)).trans hgap
  have hgB : primalGapThreshold * p.ε ^ 2 ≤ p.L * p.gap :=
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (sq_nonneg _)).trans hgap
  have hgC : 80 * p.ε ^ 2 ≤ p.L * p.gap :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)).trans hgap
  have ha := accelerated_budget_lower p hκA hgA hN
  have hb := primal_stochastic_budget_lower p hκB hgB hN
  have hc := (testing_nontrivial_budget_lower p hκC hgC hN).2
  have hd := localization_nontrivial_budget_lower p hκC hgC hN
  have hpos := upperRate_components p
  have hl : 0 ≤ p.localization := mul_nonneg (Real.sqrt_nonneg _) (le_max_left _ _)
  have hb' : primalLowerCoefficient * p.stochastic ≤ N := by
    have h0 := mul_nonneg primalLowerCoefficient_pos.le (outerGapRatio_nonneg p)
    change 0 ≤ primalLowerCoefficient * (p.L * p.gap / p.ε ^ 2) at h0
    linarith only [hb, h0]
  have hbds := localizedLowerBase_bounds
  exact four_lower_bounds
    ((mul_le_mul_of_nonneg_right hbds.1 hpos.1).trans ha)
    ((mul_le_mul_of_nonneg_right hbds.2.1 hpos.2.1).trans hb')
    ((mul_le_mul_of_nonneg_right hbds.2.2.1 hpos.2.2.1).trans hc)
    ((mul_le_mul_of_nonneg_right hbds.2.2.2 hl).trans hd)

theorem localized_complexity_lower (p : Parameters) (hκ : localizedConditionThreshold ≤ p.κ)
    (hgap : localizedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap) :
    (⌈localizedLowerCoefficient * p.rate⌉₊ : ℕ∞) ≤ localizedComplexity p := by
  unfold localizedComplexity oracleComplexity
  apply le_iInf
  intro N
  exact_mod_cast Nat.ceil_le.mpr (localized_budget_lower p hκ hgap N.property)

theorem localized_lower_statement : LocalizedLowerStatement :=
  ⟨localizedLowerCoefficient, localizedGapThreshold, localizedConditionThreshold,
    localizedLowerCoefficient_pos, localizedGapThreshold_pos, localizedConditionThreshold_pos,
    fun p hκ hgap _ hN => localized_budget_lower p hκ hgap hN⟩

end FreshGradientMinimax
