import MatchingBounds1005.CalendarCalibration
import MatchingBounds1005.PowerDimension

/-! A fixed floor query budget with the final unqueried candidate strictly
before the last readout's disclosure time. -/
noncomputable section

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration

def candidateThreshold (p : ℕ) : ℝ := min (parameterThreshold p) (horizonLower p / 8)

theorem candidateThreshold_pos (p : ℕ) : 0 < candidateThreshold p :=
  lt_min (parameterThreshold_pos p) (div_pos (horizonLower_pos p) (by norm_num))

def candidateBudget (p : ℕ) (t : ℝ) : ℕ := Nat.floor ((horizonLower p / 8) * Model.rate (t ^ 3))

theorem candidateBudget_safe (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ candidateThreshold p) : candidateBudget p t + 1 < calendarHorizon p t := by
  have hp : t ≤ parameterThreshold p := hsmall.trans (min_le_left _ _)
  have hc : t ≤ horizonLower p / 8 := hsmall.trans (min_le_right _ _)
  have ht1 := hp.trans (parameterThreshold_le_one p)
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  have ht5 : t ^ 5 ≤ t := by nlinarith only [mul_le_mul_of_nonneg_left ht4 ht.le]
  let x := (horizonLower p / 8) * Model.rate (t ^ 3)
  have hx : x = (horizonLower p / 8) / t ^ 5 := by dsimp [x]; rw [cube_rate ht, mul_one_div]
  have hx1 : 1 ≤ x := by rw [hx]; exact (le_div_iff₀ (pow_pos ht 5)).mpr (by linarith)
  have hf : (candidateBudget p t : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx1)
  have hcal := (calendarHorizon_bounds p t ht hp).1
  have hcal' : 4 * x ≤ (calendarHorizon p t : ℝ) := by
    convert hcal using 1
    dsimp [x]
    ring
  have hfinal : (candidateBudget p t : ℝ) + 1 < (calendarHorizon p t : ℝ) := by
    linarith only [hf, hx1, hcal']
  exact_mod_cast hfinal

theorem candidateBudget_le_baseSize (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ candidateThreshold p) : candidateBudget p t ≤
      phaseCount (amplitudeConstant p) t * PathGreen.pathSize (pathScale (amplitudeConstant p) (scale p) t) := by
  have hs := candidateBudget_safe p t ht hsmall
  have hu := (calendarHorizon_integer_bounds p t ht (hsmall.trans (min_le_left _ _))).2
  omega

theorem candidateBudget_pos (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ candidateThreshold p) : 1 ≤ candidateBudget p t := by
  have hp : t ≤ parameterThreshold p := hsmall.trans (min_le_left _ _)
  have hc : t ≤ horizonLower p / 8 := hsmall.trans (min_le_right _ _)
  have ht1 := hp.trans (parameterThreshold_le_one p)
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.le ht1
  have ht5 : t ^ 5 ≤ horizonLower p / 8 := by
    nlinarith only [hc, mul_le_mul_of_nonneg_left ht4 ht.le]
  apply Nat.le_floor
  rw [cube_rate ht, mul_one_div]
  exact (le_div_iff₀ (pow_pos ht 5)).mpr (by simpa only [Nat.cast_one, one_mul] using ht5)

end MatchingBounds1005.AnalyticFamily
