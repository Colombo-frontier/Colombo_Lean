import FreshGradientMinimax.LocalizedLogEquivalence

/-! Corollary 3.5 follows at sigma = 0. Its lower bound here uses only
the two exact-oracle mechanisms E.3 and B.3, without any noise limit. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem exact_mechanisms_budget_lower (p : Parameters) (hκ : localizedConditionThreshold ≤ p.κ)
    (hgap : localizedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap)
    {N : ℕ} (hN : BudgetSuffices p (some p.G) N) :
    localizedLowerCoefficient * (p.deterministic + p.localization) ≤ N := by
  have hκA : acceleratedConditionThreshold ≤ p.κ := ((le_max_left _ _).trans (le_max_left _ _)).trans hκ
  have hκB : 8192 ≤ p.κ := (le_max_right _ _).trans hκ
  have hgA : acceleratedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap :=
    (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (sq_nonneg _)).trans hgap
  have hgB : 80 * p.ε ^ 2 ≤ p.L * p.gap :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)).trans hgap
  have ha := accelerated_budget_lower p hκA hgA hN
  have hb := localization_nontrivial_budget_lower p hκB hgB hN
  have hd0 := (upperRate_components p).1
  have hl0 : 0 ≤ p.localization := mul_nonneg (Real.sqrt_nonneg _) (le_max_left _ _)
  have ha' := (mul_le_mul_of_nonneg_right localizedLowerBase_bounds.1 hd0).trans ha
  have hb' := (mul_le_mul_of_nonneg_right localizedLowerBase_bounds.2.2.2 hl0).trans hb
  unfold localizedLowerCoefficient
  linarith only [ha', hb', Nat.cast_nonneg (α := ℝ) N]

theorem exact_mechanisms_complexity_lower (p : Parameters) (hκ : localizedConditionThreshold ≤ p.κ)
    (hgap : localizedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap) :
    (⌈localizedLowerCoefficient * (p.deterministic + p.localization)⌉₊ : ℕ∞) ≤ localizedComplexity p := by
  unfold localizedComplexity oracleComplexity
  apply le_iInf
  intro N
  exact_mod_cast Nat.ceil_le.mpr (exact_mechanisms_budget_lower p hκ hgap N.property)

theorem localized_regime_nontrivial (p : Parameters)
    (hgap : localizedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap) : p.ε ^ 2 ≤ p.L * p.gap := by
  have hc : (1 : ℝ) ≤ localizedGapThreshold := (by norm_num : (1 : ℝ) ≤ 80).trans (le_max_right _ _)
  have h := mul_le_mul_of_nonneg_right hc (sq_nonneg p.ε)
  simpa only [one_mul] using h.trans hgap

theorem corollary_35 :
    ∃ c C₁ C₀ κ₀ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₀ ∧ 0 < κ₀ ∧
      ∀ p : Parameters, p.σ = 0 → κ₀ ≤ p.κ → C₀ * p.ε ^ 2 ≤ p.L * p.gap →
        (⌈c * (p.deterministic + p.localization)⌉₊ : ℕ∞) ≤ localizedComplexity p ∧
        ∃ N : ℕ, BudgetSuffices p (some p.G) N ∧
          (N : ℝ) ≤ C₁ * logarithmicEnvelope p ^ 11 * (p.deterministic + p.localization) := by
  refine ⟨localizedLowerCoefficient, 10 ^ 202, localizedGapThreshold, localizedConditionThreshold,
    localizedLowerCoefficient_pos, by norm_num, localizedGapThreshold_pos, localizedConditionThreshold_pos, ?_⟩
  intro p hσ hκ hgap
  refine ⟨exact_mechanisms_complexity_lower p hκ hgap, ?_⟩
  have h := localized_upper_rate_bound p (localized_regime_nontrivial p hgap)
  simpa only [p.noise_free_rate hσ] using h

end FreshGradientMinimax
