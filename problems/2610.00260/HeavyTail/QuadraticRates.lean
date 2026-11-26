import HeavyTail.SharpRates

/-! Expanded upper bound and the full quadratic matching statistical rate,
retaining the trace contribution alongside both heavy-tail terms. -/
noncomputable section
open scoped ENNReal
namespace HeavyTail
universe u

theorem expanded_strongly_convex_upper
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (θ : OracleParameters) (hT : 0 < θ.T) (hμ : 0 < θ.μ) :
    atMostCallMinimax E θ ≤ ENNReal.ofReal
      ((4 * unifiedUpperConstant θ.p / θ.μ) *
        expandedStatisticalScale θ.G θ.L θ.s θ.p θ.δ θ.T) := by
  apply (unified_atMostCallMinimax_upper (E := E) θ hT).trans
  apply ENNReal.ofReal_le_ofReal
  have hv := (optimizationAmplitude_pos θ hT).le
  have he := (envelope_mono θ.μ_nonneg θ.D_pos.le (le_min θ.G_pos.le hv) (min_le_right _ _)).trans
    (envelope_le_quadratic hμ)
  have hs := optimizationAmplitude_square_expanded θ hT
  have hdiv := div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 2 * θ.μ)
  have hh := mul_le_mul_of_nonneg_left (he.trans hdiv) (unifiedUpperConstant_pos θ.p).le
  convert hh using 1 <;> ring

theorem full_quadratic_statistical_rate {d : ℕ} (θ : OracleParameters) (hT : 0 < θ.T)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) (hμ : 0 < θ.μ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hmatch : θ.G / Real.sqrt θ.T + θ.G * confidenceLog θ.δ / θ.T ≤
      C₀ * statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T)
    (hbranch : statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T ≤ min θ.G (θ.μ * θ.D)) :
    ENNReal.ofReal ((1 / 1179648 : ℝ) * (quadraticStatisticalScale θ.L θ.s θ.p θ.δ θ.T / θ.μ)) ≤
      atMostCallMinimax (HardSpace d) θ ∧
    atMostCallMinimax (HardSpace d) θ ≤ ENNReal.ofReal
      ((2 * unifiedUpperConstant θ.p * (C₀ + 1) ^ 2) *
        (quadraticStatisticalScale θ.L θ.s θ.p θ.δ θ.T / θ.μ)) := by
  obtain ⟨hl, hu⟩ := matching_statistical_minimax θ hT hdim hC₀ hmatch
  rw [min_eq_right (le_min_iff.mp hbranch).1, envelope_quadratic hμ (le_min_iff.mp hbranch).2] at hl hu
  have hs := statisticalAmplitude_square_comparison θ hT
  have hlo := div_le_div_of_nonneg_right hs.1 hμ.le
  have hhi := div_le_div_of_nonneg_right hs.2 hμ.le
  simp only [mul_div_assoc] at hlo hhi
  have he : (statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T) ^ 2 / (2 * θ.μ) =
      ((statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T) ^ 2 / θ.μ) / 2 := by ring
  rw [he] at hl hu
  refine ⟨(ENNReal.ofReal_le_ofReal ?_).trans hl, hu.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · nlinarith only [hlo]
  · have hh := mul_le_mul_of_nonneg_left hhi
      (mul_nonneg (unifiedUpperConstant_pos θ.p).le (sq_nonneg (C₀ + 1)))
    nlinarith only [hh]

end HeavyTail
