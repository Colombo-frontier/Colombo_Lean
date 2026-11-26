import FreshGradientMinimax.PrimalRateConstants

/-! The complete dimension-free C lower rate, including integer budgets and
zero noise, obtained from the proved finite-coordinate hard distribution. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem primal_stochastic_budget_lower (p : Parameters)
    (hκ : 4 * primalScalingConstant ≤ p.κ)
    (hgap : primalGapThreshold * p.ε ^ 2 ≤ p.L * p.gap)
    {N : ℕ} (hN : BudgetSuffices p (some p.G) N) :
    primalLowerCoefficient * (p.L * p.gap / p.ε ^ 2 + p.stochastic) ≤ N := by
  have hL := p.μ_pos.trans_le p.μ_le_L
  have ha := primalValueCoefficient_pos
  have hnoise := primalNoiseCoefficient_pos
  have hlam := primalValueScale_pos hL p.ε_pos
  obtain ⟨n, hn, hfloor, hcount⟩ := primal_stage_count_exists hlam (primal_gap_threshold_scale p hgap)
  have hh := (primal_floor_budget_strict p n hn hκ hfloor hN).le
  have hp := primalRevealProbability_pos hL p.ε_pos p.μ_pos p.σ
  have hh' := (div_le_iff₀ (by positivity : 0 < 12 * primalRevealProbability p.L p.ε p.μ p.σ)).mp hh
  have he : p.gap / (64 * primalValueScale p.L p.ε) =
      (p.L * p.gap / p.ε ^ 2) / (64 * primalValueCoefficient) := by
    rw [primalValueScale_coefficient]
    field_simp [hL.ne', p.ε_pos.ne', primalValueCoefficient_pos.ne']
    ring
  rw [he] at hcount
  have hb := (div_le_iff₀ (by positivity : 0 < 64 * primalValueCoefficient)).mp hcount
  have hb' : p.L * p.gap / p.ε ^ 2 ≤
      (768 * primalValueCoefficient * (N : ℝ)) * primalRevealProbability p.L p.ε p.μ p.σ := by
    have h := mul_le_mul_of_nonneg_right hh' (show 0 ≤ 64 * primalValueCoefficient by positivity)
    nlinarith only [hb, h]
  have hZ : 0 ≤ 768 * primalValueCoefficient * (N : ℝ) := by positivity
  have hb0 : p.L * p.gap / p.ε ^ 2 ≤ 768 * primalValueCoefficient * (N : ℝ) :=
    hb'.trans (mul_le_of_le_one_right hZ (primalRevealProbability_le_one p.L p.ε p.μ p.σ))
  have hX : 0 ≤ p.κ * p.σ ^ 2 / p.ε ^ 2 := by
    exact div_nonneg (mul_nonneg (div_nonneg hL.le p.μ_pos.le) (sq_nonneg p.σ)) (sq_nonneg p.ε)
  have hs : p.stochastic ≤ (768 * primalValueCoefficient * (N : ℝ)) * primalNoiseCoefficient := by
    have h1 := mul_le_mul_of_nonneg_right hb' hX
    have h2 := mul_le_mul_of_nonneg_left (primal_noise_probability_bound p) hZ
    have he : (p.L * p.gap / p.ε ^ 2) * (p.κ * p.σ ^ 2 / p.ε ^ 2) = p.stochastic := by
      unfold Parameters.stochastic
      field_simp
      ring
    rw [he] at h1
    exact h1.trans (by simpa only [mul_assoc] using h2)
  rw [primalLowerCoefficient, ← div_eq_inv_mul]
  apply (div_le_iff₀ (by positivity :
    0 < 768 * primalValueCoefficient * (1 + primalNoiseCoefficient))).mpr
  nlinarith only [hb0, hs]

theorem primal_stochastic_complexity_lower (p : Parameters)
    (hκ : 4 * primalScalingConstant ≤ p.κ)
    (hgap : primalGapThreshold * p.ε ^ 2 ≤ p.L * p.gap) :
    (⌈primalLowerCoefficient * (p.L * p.gap / p.ε ^ 2 + p.stochastic)⌉₊ : ℕ∞) ≤ localizedComplexity p := by
  unfold localizedComplexity oracleComplexity
  apply le_iInf
  intro N
  exact_mod_cast Nat.ceil_le.mpr (primal_stochastic_budget_lower p hκ hgap N.property)

theorem primal_stochastic_lower_statement :
    ∃ c C₀ κ₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ 0 < κ₀ ∧
      ∀ p : Parameters, κ₀ ≤ p.κ → C₀ * p.ε ^ 2 ≤ p.L * p.gap →
        ∀ N : ℕ, BudgetSuffices p (some p.G) N →
          c * (p.L * p.gap / p.ε ^ 2 + p.stochastic) ≤ N := by
  refine ⟨primalLowerCoefficient, primalGapThreshold, 4 * primalScalingConstant,
    primalLowerCoefficient_pos, primalGapThreshold_pos, ?_, ?_⟩
  · norm_num [primalScalingConstant]
  · intro p hκ hgap N hN
    exact primal_stochastic_budget_lower p hκ hgap hN

end FreshGradientMinimax
