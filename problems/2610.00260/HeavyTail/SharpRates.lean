import HeavyTail.MatchingRates
import HeavyTail.StatisticalSquares

/-! The sharp heavy-tail minimax rates in cor:heavy, with explicit positive
comparison constants. Rates are derived from the actual all-budget theorem. -/
noncomputable section
open scoped ENNReal
namespace HeavyTail

def convexHeavyRate (D L s p δ : ℝ) (T : ℕ) : ℝ :=
  D * (s * (L ^ 2 / s ^ 2) ^ (1 - 1 / p) + s * (confidenceLog δ) ^ (1 - 1 / p)) /
    (T : ℝ) ^ (1 - 1 / p)

theorem convexHeavyRate_eq (D L s p δ : ℝ) (T : ℕ) :
    convexHeavyRate D L s p δ T = D *
      (heavyDimensionTerm L s p T + heavyConfidenceTerm s p δ T) := by
  unfold convexHeavyRate heavyDimensionTerm heavyConfidenceTerm
  ring

theorem heavy_envelope_minimax {d : ℕ} (θ : OracleParameters) (hT : 0 < θ.T)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hsat : heavyAmplitude θ.L θ.s θ.p θ.δ θ.T ≤ θ.G)
    (hdom : θ.G / Real.sqrt θ.T + θ.G * confidenceLog θ.δ / θ.T + θ.L / Real.sqrt θ.T ≤
      C₀ * heavyAmplitude θ.L θ.s θ.p θ.δ θ.T) :
    ENNReal.ofReal ((1 / 147456 : ℝ) * envelope θ.μ θ.D
      (heavyAmplitude θ.L θ.s θ.p θ.δ θ.T)) ≤ atMostCallMinimax (HardSpace d) θ ∧
    atMostCallMinimax (HardSpace d) θ ≤ ENNReal.ofReal
      ((unifiedUpperConstant θ.p * (C₀ + 1) ^ 2) * envelope θ.μ θ.D
        (heavyAmplitude θ.L θ.s θ.p θ.δ θ.T)) := by
  obtain ⟨hl, hu⟩ := unified_all_budget θ hT hdim
  have hs := θ.s_pos
  have hell := (confidenceLog_pos θ.δ_pos θ.δ_lt_tenth).le
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hu0 : 0 ≤ heavyAmplitude θ.L θ.s θ.p θ.δ θ.T := by unfold heavyAmplitude; positivity
  have htrace : 0 ≤ θ.L / Real.sqrt θ.T := by positivity
  have hlow : heavyAmplitude θ.L θ.s θ.p θ.δ θ.T ≤
      min θ.G (statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T) := by
    apply le_min hsat
    rw [statisticalAmplitude_eq_trace_heavy]
    linarith only [htrace]
  refine ⟨(ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (envelope_mono θ.μ_nonneg θ.D_pos.le hu0 hlow) (by norm_num))).trans hl, hu.trans ?_⟩
  have hv : optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ θ.T ≤
      (C₀ + 1) * heavyAmplitude θ.L θ.s θ.p θ.δ θ.T := by
    rw [optimizationAmplitude_eq_transients, statisticalAmplitude_eq_trace_heavy]
    nlinarith only [hdom]
  have he := envelope_min_amplitude_scale_upper θ.μ_nonneg θ.D_pos.le θ.G_pos.le
    (optimizationAmplitude_pos θ hT).le (by linarith : 1 ≤ C₀ + 1) hv
  rw [min_eq_right hsat] at he
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (unifiedUpperConstant_pos θ.p).le

theorem sharp_convex_heavy_rate {d : ℕ} (θ : OracleParameters) (hT : 0 < θ.T)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) (hμ : θ.μ = 0) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hsat : heavyAmplitude θ.L θ.s θ.p θ.δ θ.T ≤ θ.G)
    (hdom : θ.G / Real.sqrt θ.T + θ.G * confidenceLog θ.δ / θ.T + θ.L / Real.sqrt θ.T ≤
      C₀ * heavyAmplitude θ.L θ.s θ.p θ.δ θ.T) :
    ENNReal.ofReal ((1 / 294912 : ℝ) * convexHeavyRate θ.D θ.L θ.s θ.p θ.δ θ.T) ≤
      atMostCallMinimax (HardSpace d) θ ∧
    atMostCallMinimax (HardSpace d) θ ≤ ENNReal.ofReal
      ((unifiedUpperConstant θ.p * (C₀ + 1) ^ 2) * convexHeavyRate θ.D θ.L θ.s θ.p θ.δ θ.T) := by
  obtain ⟨hl, hu⟩ := heavy_envelope_minimax θ hT hdim hC₀ hsat hdom
  rw [hμ, envelope_zero_curvature] at hl hu
  have hs := heavyAmplitude_split θ
  have hlo := mul_le_mul_of_nonneg_left hs.2 θ.D_pos.le
  have hhi := mul_le_mul_of_nonneg_left hs.1 θ.D_pos.le
  rw [← convexHeavyRate_eq] at hlo hhi
  refine ⟨(ENNReal.ofReal_le_ofReal ?_).trans hl, hu.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · nlinarith only [hlo]
  · exact mul_le_mul_of_nonneg_left hhi (mul_nonneg (unifiedUpperConstant_pos θ.p).le (sq_nonneg _))

theorem sharp_strongly_convex_heavy_rate {d : ℕ} (θ : OracleParameters) (hT : 0 < θ.T)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) (hμ : 0 < θ.μ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hsat : heavyAmplitude θ.L θ.s θ.p θ.δ θ.T ≤ θ.G)
    (hcurv : heavyAmplitude θ.L θ.s θ.p θ.δ θ.T ≤ θ.μ * θ.D)
    (hdom : θ.G / Real.sqrt θ.T + θ.G * confidenceLog θ.δ / θ.T + θ.L / Real.sqrt θ.T ≤
      C₀ * heavyAmplitude θ.L θ.s θ.p θ.δ θ.T) :
    ENNReal.ofReal ((1 / 1179648 : ℝ) * (heavySquareScale θ.L θ.s θ.p θ.δ θ.T / θ.μ)) ≤
      atMostCallMinimax (HardSpace d) θ ∧
    atMostCallMinimax (HardSpace d) θ ≤ ENNReal.ofReal
      ((unifiedUpperConstant θ.p * (C₀ + 1) ^ 2) * (heavySquareScale θ.L θ.s θ.p θ.δ θ.T / θ.μ)) := by
  obtain ⟨hl, hu⟩ := heavy_envelope_minimax θ hT hdim hC₀ hsat hdom
  rw [envelope_quadratic hμ hcurv] at hl hu
  have hs := heavyAmplitude_square_comparison θ
  have hlo := div_le_div_of_nonneg_right hs.1 hμ.le
  have hhi := div_le_div_of_nonneg_right hs.2 hμ.le
  simp only [mul_div_assoc] at hlo hhi
  have he : (heavyAmplitude θ.L θ.s θ.p θ.δ θ.T) ^ 2 / (2 * θ.μ) =
      ((heavyAmplitude θ.L θ.s θ.p θ.δ θ.T) ^ 2 / θ.μ) / 2 := by ring
  rw [he] at hl hu
  refine ⟨(ENNReal.ofReal_le_ofReal ?_).trans hl, hu.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · nlinarith only [hlo]
  · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (unifiedUpperConstant_pos θ.p).le (sq_nonneg _))
    nlinarith only [hhi]

end HeavyTail
