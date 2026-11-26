import FreshGradientMinimax.PathSignalGrowth
import FreshGradientMinimax.UnlocalizedLower

/-! The complete localization logarithm of Corollary B.3, with the original
1/1024 constant. The actual hard family rules out every budget below the real
threshold, so no monotonicity or padding assumption about algorithms is needed. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem path_localization_condition (p : Parameters) (hκ : 8192 ≤ p.κ) : 4 * p.μ ≤ p.L := by
  have h := (le_div_iff₀ p.μ_pos).mp hκ
  linarith [p.μ_pos]

theorem localization_budget_strict (p : Parameters) (hκ : 8192 ≤ p.κ)
    (hgap : 80 * p.ε ^ 2 / p.L ≤ p.gap) (hb : 1 < p.G / (p.ε * Real.sqrt p.κ))
    {N : ℕ} (hN : BudgetSuffices p (some p.G) N) :
    Real.sqrt p.κ * Real.log (p.G / (p.ε * Real.sqrt p.κ)) / 1024 < (N : ℝ) := by
  apply lt_of_not_ge
  intro hle
  exact localized_label_horizon_impossible p (path_localization_condition p hκ) hgap N
    (pathHardSignal_horizon_le p hκ hb hle) hN

theorem localization_budget_lower (p : Parameters) (hκ : 8192 ≤ p.κ)
    (hgap : 80 * p.ε ^ 2 / p.L ≤ p.gap)
    {N : ℕ} (hN : BudgetSuffices p (some p.G) N) :
    (1 / 1024 : ℝ) * p.localization ≤ N := by
  have hb0 : 0 ≤ p.G / (p.ε * Real.sqrt p.κ) :=
    div_nonneg p.G_nonneg (mul_nonneg p.ε_pos.le (Real.sqrt_nonneg _))
  by_cases hb : p.G / (p.ε * Real.sqrt p.κ) ≤ 1
  · have hl := Real.log_nonpos hb0 hb
    simpa only [Parameters.localization, logPlus, max_eq_left hl, mul_zero] using (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  · have hb' : 1 < p.G / (p.ε * Real.sqrt p.κ) := lt_of_not_ge hb
    have h := (localization_budget_strict p hκ hgap hb' hN).le
    have hl := (Real.log_pos hb').le
    unfold Parameters.localization logPlus
    rw [max_eq_right hl]
    convert h using 1
    ring

theorem localization_nontrivial_budget_lower (p : Parameters) (hκ : 8192 ≤ p.κ)
    (hgap : 80 * p.ε ^ 2 ≤ p.L * p.gap)
    {N : ℕ} (hN : BudgetSuffices p (some p.G) N) :
    (1 / 1024 : ℝ) * p.localization ≤ N := by
  apply localization_budget_lower p hκ _ hN
  apply (div_le_iff₀ (p.μ_pos.trans_le p.μ_le_L)).mpr
  nlinarith only [hgap]

theorem corollary_B3 (p : Parameters) (hκ : 8192 ≤ p.κ)
    (hgap : 80 * p.ε ^ 2 / p.L ≤ p.gap) :
    (⌈(1 / 1024 : ℝ) * p.localization⌉₊ : ℕ∞) ≤ localizedComplexity p := by
  unfold localizedComplexity oracleComplexity
  apply le_iInf
  intro N
  exact_mod_cast Nat.ceil_le.mpr (localization_budget_lower p hκ hgap N.property)

end FreshGradientMinimax
