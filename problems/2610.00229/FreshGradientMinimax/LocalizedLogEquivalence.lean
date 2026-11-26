import FreshGradientMinimax.MainTheorem34

/-! The displayed upper rate differs from the four-term lower rate only
by logarithms independent of G. The entire G dependence stays linear in
the single localization term. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem log_two_add_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.log (2 + a + b) ≤ Real.log (2 + a) + Real.log (2 + b) := by
  have h := Real.log_le_log (by positivity : 0 < 2 + a + b)
    (show 2 + a + b ≤ (2 + a) * (2 + b) by nlinarith only [ha, hb, mul_nonneg ha hb])
  rwa [Real.log_mul (by positivity) (by positivity)] at h

theorem log_two_square_bound {a : ℝ} (ha : 0 ≤ a) :
    Real.log (2 + a ^ 2) ≤ 2 * Real.log (2 + a) := by
  have h := Real.log_le_log (by positivity : 0 < 2 + a ^ 2)
    (show 2 + a ^ 2 ≤ (2 + a) ^ 2 by nlinarith only [ha])
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem log_two_cube_bound {a : ℝ} (ha : 0 ≤ a) :
    Real.log (2 + a ^ 3) ≤ 3 * Real.log (2 + a) := by
  have h := Real.log_le_log (by positivity : 0 < 2 + a ^ 3)
    (show 2 + a ^ 3 ≤ (2 + a) ^ 3 by nlinarith only [ha, sq_nonneg a])
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem log_two_square_logPlus {b : ℝ} (hb : 0 ≤ b) :
    Real.log (2 + b ^ 2) ≤ 2 + 2 * logPlus b := by
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hl0 : 0 ≤ logPlus b := le_max_left _ _
  by_cases h : b ≤ 1
  · have hs : 2 + b ^ 2 ≤ (3 : ℝ) := by nlinarith only [hb, h]
    have hh := Real.log_le_log (by positivity : 0 < 2 + b ^ 2) hs
    linarith only [hh, hlog3, hl0]
  · have hb1 : 1 < b := lt_of_not_ge h
    have hs : 2 + b ^ 2 ≤ 3 * b ^ 2 := by nlinarith only [hb1]
    have hh := Real.log_le_log (by positivity : 0 < 2 + b ^ 2) hs
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
    have hll : Real.log b ≤ logPlus b := le_max_right _ _
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, hlog3, hll]

theorem outerColdLog_localization (p : Parameters) :
    outerColdLog p ≤ 8 * logarithmicEnvelope p + 2 * logPlus (p.G / (p.ε * Real.sqrt p.κ)) := by
  have hk : 0 < p.κ := lt_of_lt_of_le (by norm_num) p.condition_ge_one
  have hb : 0 ≤ p.G / (p.ε * Real.sqrt p.κ) :=
    div_nonneg p.G_nonneg (mul_nonneg p.ε_pos.le (Real.sqrt_nonneg _))
  have hq := outerGapRatio_nonneg p
  have he : p.κ ^ 3 * (p.G / (p.ε * Real.sqrt p.κ)) ^ 2 = p.κ ^ 2 * p.G ^ 2 / p.ε ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hk.le]
    field_simp [p.ε_pos.ne', hk.ne']
    ring
  have h1 := log_two_add_bound (a := p.κ ^ 3 * (p.G / (p.ε * Real.sqrt p.κ)) ^ 2)
    (b := p.κ ^ 2 * outerGapRatio p) (by positivity) (by positivity)
  have h2 := log_two_mul_bound (show 0 ≤ p.κ ^ 3 by positivity) (sq_nonneg (p.G / (p.ε * Real.sqrt p.κ)))
  have h3 := log_two_mul_bound (sq_nonneg p.κ) hq
  have h4 := log_two_cube_bound hk.le
  have h5 := log_two_square_bound hk.le
  have h6 := log_two_square_logPlus hb
  rw [he] at h1 h2
  have hΛ := logarithmicEnvelope_bounds p
  change Real.log (2 + p.κ ^ 2 * p.G ^ 2 / p.ε ^ 2 + p.κ ^ 2 * outerGapRatio p) ≤ _
  linarith only [h1, h2, h3, h4, h5, h6, hΛ.1, hΛ.2.1, hΛ.2.2.1]

theorem upperRate_log_equivalence (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) :
    upperRate p ≤ 12 * logarithmicEnvelope p * p.rate := by
  have hΛ := (logarithmicEnvelope_bounds p).1
  have hpos := upperRate_components p
  have hl : 0 ≤ p.localization := mul_nonneg (Real.sqrt_nonneg _) (le_max_left _ _)
  have hr : 0 ≤ p.rate := by unfold Parameters.rate; linarith only [hpos.1, hpos.2.1, hpos.2.2.1, hl]
  have hD : Real.sqrt p.κ ≤ p.deterministic := by
    rw [outer_deterministic_identity]
    exact le_mul_of_one_le_right (Real.sqrt_nonneg _) (outerGapRatio_one p hreg)
  have hlog := mul_le_mul_of_nonneg_left (outerColdLog_localization p) (Real.sqrt_nonneg p.κ)
  have hD' := mul_le_mul_of_nonneg_left hD (show 0 ≤ 8 * logarithmicEnvelope p by linarith only [hΛ])
  have hcore : p.deterministic + p.stochastic + p.testing ≤ p.rate := by unfold Parameters.rate; linarith only [hl]
  have hDr : p.deterministic ≤ p.rate := by unfold Parameters.rate; linarith only [hpos.2.1, hpos.2.2.1, hl]
  have hlr : p.localization ≤ p.rate := by unfold Parameters.rate; linarith only [hpos.1, hpos.2.1, hpos.2.2.1]
  have hD'' := mul_le_mul_of_nonneg_left hDr (show 0 ≤ 8 * logarithmicEnvelope p by linarith only [hΛ])
  have hΛr := mul_le_mul_of_nonneg_right hΛ hr
  rw [upperRate_identity]
  change p.deterministic + p.stochastic + p.testing + Real.sqrt p.κ * outerColdLog p ≤ _
  have hid : Real.sqrt p.κ * logPlus (p.G / (p.ε * Real.sqrt p.κ)) = p.localization := rfl
  nlinarith only [hlog, hD', hcore, hlr, hD'', hΛr, hid, hr]

theorem localized_upper_rate_bound (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) :
    ∃ N : ℕ, BudgetSuffices p (some p.G) N ∧
      (N : ℝ) ≤ 10 ^ 202 * logarithmicEnvelope p ^ 11 * p.rate := by
  obtain ⟨N, hN, hu⟩ := localized_upper_bound p hreg
  refine ⟨N, hN, hu.trans ?_⟩
  have hΛ := (logarithmicEnvelope_bounds p).1
  have h := mul_le_mul_of_nonneg_left (upperRate_log_equivalence p hreg)
    (show 0 ≤ 10 ^ 200 * logarithmicEnvelope p ^ 10 by positivity)
  have hr : 0 ≤ p.rate := by
    have hp := upperRate_components p
    have hl : 0 ≤ p.localization := mul_nonneg (Real.sqrt_nonneg _) (le_max_left _ _)
    unfold Parameters.rate
    linarith only [hp.1, hp.2.1, hp.2.2.1, hl]
  have hnon : 0 ≤ logarithmicEnvelope p ^ 11 * p.rate := by positivity
  calc
    _ ≤ (10 ^ 200 * logarithmicEnvelope p ^ 10) * (12 * logarithmicEnvelope p * p.rate) := h
    _ = (12 * 10 ^ 200) * (logarithmicEnvelope p ^ 11 * p.rate) := by ring
    _ ≤ _ := by nlinarith only [hnon]

end FreshGradientMinimax
