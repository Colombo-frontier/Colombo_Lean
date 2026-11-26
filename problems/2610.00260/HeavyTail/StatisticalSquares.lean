import HeavyTail.StatisticalAlgebra

/-! Squared-rate comparisons, including the finite-variance term and the
expanded upper expression displayed in the manuscript. -/
noncomputable section
namespace HeavyTail

theorem traceTerm_square (L : ℝ) {T : ℕ} (hT : 0 < T) :
    (L / Real.sqrt T) ^ 2 = L ^ 2 / T := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem statisticalAmplitude_square_comparison (θ : OracleParameters) (hT : 0 < θ.T) :
    quadraticStatisticalScale θ.L θ.s θ.p θ.δ θ.T ≤
        4 * (statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T) ^ 2 ∧
    (statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T) ^ 2 ≤
        4 * quadraticStatisticalScale θ.L θ.s θ.p θ.δ θ.T := by
  have hs := θ.s_pos
  have hell := (confidenceLog_pos θ.δ_pos θ.δ_lt_tenth).le
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have ht : 0 ≤ θ.L / Real.sqrt θ.T := by positivity
  have hu : 0 ≤ heavyAmplitude θ.L θ.s θ.p θ.δ θ.T := by unfold heavyAmplitude; positivity
  have hh := heavyAmplitude_square_comparison θ
  have htrace := traceTerm_square θ.L hT
  rw [statisticalAmplitude_eq_trace_heavy]
  unfold quadraticStatisticalScale
  constructor
  · nlinarith only [hh.1, htrace, mul_nonneg ht hu, sq_nonneg (θ.L / Real.sqrt θ.T)]
  · nlinarith only [hh.2, htrace,
      sq_nonneg (θ.L / Real.sqrt θ.T - heavyAmplitude θ.L θ.s θ.p θ.δ θ.T),
      sq_nonneg (θ.L / Real.sqrt θ.T)]

def expandedStatisticalScale (G L s p δ : ℝ) (T : ℕ) : ℝ :=
  (G ^ 2 + L ^ 2) / T + G ^ 2 * (confidenceLog δ) ^ 2 / (T : ℝ) ^ 2 +
    heavySquareScale L s p δ T

theorem optimizationAmplitude_square_expanded (θ : OracleParameters) (hT : 0 < θ.T) :
    (optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ θ.T) ^ 2 ≤
      8 * expandedStatisticalScale θ.G θ.L θ.s θ.p θ.δ θ.T := by
  let a := θ.G / Real.sqrt θ.T
  let b := θ.G * confidenceLog θ.δ / θ.T
  let c := θ.L / Real.sqrt θ.T
  let u := heavyAmplitude θ.L θ.s θ.p θ.δ θ.T
  have he : optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ θ.T = a + b + c + u := by
    unfold optimizationAmplitude
    rw [statisticalAmplitude_eq_trace_heavy]
    dsimp [a, b, c, u]
    ring
  have hsum : (a + b + c + u) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + u ^ 2) := by
    nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - u),
      sq_nonneg (b - c), sq_nonneg (b - u), sq_nonneg (c - u)]
  have hu := (heavyAmplitude_square_comparison θ).2
  have ha : a ^ 2 = θ.G ^ 2 / θ.T := traceTerm_square θ.G hT
  have hc : c ^ 2 = θ.L ^ 2 / θ.T := traceTerm_square θ.L hT
  have hb : b ^ 2 = θ.G ^ 2 * (confidenceLog θ.δ) ^ 2 / (θ.T : ℝ) ^ 2 := by
    simp only [b, div_pow, mul_pow]
  rw [he]
  unfold expandedStatisticalScale
  rw [add_div]
  change u ^ 2 ≤ 2 * heavySquareScale θ.L θ.s θ.p θ.δ θ.T at hu
  nlinarith only [hsum, hu, ha, hb, hc, sq_nonneg a, sq_nonneg b, sq_nonneg c]

end HeavyTail
