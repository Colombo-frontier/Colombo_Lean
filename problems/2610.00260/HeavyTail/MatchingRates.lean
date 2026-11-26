import HeavyTail.MainTheorem

/-! Matching statistical regime, saturation, and the explicit sufficient
condition from cor:matching. The conclusions concern the full minimax risk. -/
noncomputable section
open scoped ENNReal
namespace HeavyTail

theorem optimizationAmplitude_eq_transients (G L s p δ : ℝ) (T : ℕ) :
    optimizationAmplitude G L s p δ T =
      G / Real.sqrt T + G * confidenceLog δ / T + statisticalAmplitude L s p δ T := rfl

theorem statisticalAmplitude_pos (θ : OracleParameters) (hT : 0 < θ.T) :
    0 < statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T := by
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hTR : (0 : ℝ) < θ.T := Nat.cast_pos.mpr hT
  have hs := θ.s_pos
  have hell := (confidenceLog_pos θ.δ_pos θ.δ_lt_tenth).le
  unfold statisticalAmplitude
  positivity

theorem optimizationAmplitude_pos (θ : OracleParameters) (hT : 0 < θ.T) :
    0 < optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ θ.T := by
  rw [optimizationAmplitude_eq_transients]
  have hw := statisticalAmplitude_pos θ hT
  have hg := θ.G_pos
  have hell := (confidenceLog_pos θ.δ_pos θ.δ_lt_tenth).le
  positivity

theorem saturation_minimax {d : ℕ} (θ : OracleParameters) (hT : 0 < θ.T)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d)
    (hsat : θ.G ≤ statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T) :
    ENNReal.ofReal ((1 / 147456 : ℝ) * envelope θ.μ θ.D θ.G) ≤ atMostCallMinimax (HardSpace d) θ ∧
    atMostCallMinimax (HardSpace d) θ ≤ ENNReal.ofReal (unifiedUpperConstant θ.p * envelope θ.μ θ.D θ.G) := by
  obtain ⟨hl, hu⟩ := unified_all_budget θ hT hdim
  rw [min_eq_left hsat] at hl
  refine ⟨hl, hu.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (envelope_mono θ.μ_nonneg θ.D_pos.le
      (le_min θ.G_pos.le (optimizationAmplitude_pos θ hT).le) (min_le_left _ _))
    (unifiedUpperConstant_pos θ.p).le

theorem matching_statistical_minimax {d : ℕ} (θ : OracleParameters) (hT : 0 < θ.T)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hmatch : θ.G / Real.sqrt θ.T + θ.G * confidenceLog θ.δ / θ.T ≤
      C₀ * statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T) :
    ENNReal.ofReal ((1 / 147456 : ℝ) * envelope θ.μ θ.D
      (min θ.G (statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T))) ≤ atMostCallMinimax (HardSpace d) θ ∧
    atMostCallMinimax (HardSpace d) θ ≤ ENNReal.ofReal
      ((unifiedUpperConstant θ.p * (C₀ + 1) ^ 2) * envelope θ.μ θ.D
        (min θ.G (statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T))) := by
  obtain ⟨hl, hu⟩ := unified_all_budget θ hT hdim
  refine ⟨hl, hu.trans ?_⟩
  have hamp : optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ θ.T ≤
      (C₀ + 1) * statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T := by
    rw [optimizationAmplitude_eq_transients]
    nlinarith only [hmatch]
  have he := envelope_min_amplitude_scale_upper θ.μ_nonneg θ.D_pos.le θ.G_pos.le
    (optimizationAmplitude_pos θ hT).le (by linarith : 1 ≤ C₀ + 1) hamp
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left he (unifiedUpperConstant_pos θ.p).le
  simpa only [mul_assoc] using hh

theorem matching_sufficient_condition (θ : OracleParameters) (hT : 0 < θ.T)
    (hLG : θ.G ≤ θ.L)
    (hbudget : (θ.G / θ.L) ^ 2 * (confidenceLog θ.δ) ^ 2 ≤ (θ.T : ℝ)) :
    θ.G / Real.sqrt θ.T + θ.G * confidenceLog θ.δ / θ.T ≤
      2 * statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T := by
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hTR : (0 : ℝ) < θ.T := Nat.cast_pos.mpr hT
  have hell := confidenceLog_pos θ.δ_pos θ.δ_lt_tenth
  have hroot := Real.sqrt_pos.mpr hTR
  have hfirst := div_le_div_of_nonneg_right hLG hroot.le
  have hsq : (θ.G * confidenceLog θ.δ) ^ 2 ≤ (θ.L * Real.sqrt θ.T) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hTR.le]
    have hh := mul_le_mul_of_nonneg_left hbudget (sq_nonneg θ.L)
    have he : θ.L ^ 2 * ((θ.G / θ.L) ^ 2 * (confidenceLog θ.δ) ^ 2) =
        (θ.G * confidenceLog θ.δ) ^ 2 := by
      field_simp
      <;> ring
    rw [he] at hh
    simpa only [mul_pow, mul_comm (θ.L ^ 2)] using hh
  have hprod := (sq_le_sq₀ (mul_nonneg θ.G_pos.le hell.le) (mul_nonneg hL.le hroot.le)).mp hsq
  have hsecond : θ.G * confidenceLog θ.δ / θ.T ≤ θ.L / Real.sqrt θ.T := by
    apply (div_le_div_iff₀ hTR hroot).mpr
    have hh := mul_le_mul_of_nonneg_right hprod hroot.le
    calc
      _ ≤ θ.L * Real.sqrt θ.T * Real.sqrt θ.T := hh
      _ = θ.L * θ.T := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hTR.le]
  have htrace : θ.L / Real.sqrt θ.T ≤ statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T := by
    unfold statisticalAmplitude
    have hs := θ.s_pos
    exact le_add_of_nonneg_right (by positivity)
  linarith only [hfirst, hsecond, htrace]

end HeavyTail
