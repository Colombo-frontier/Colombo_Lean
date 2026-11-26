import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Radius padding and scalar-call constants for the zeroth-order upper bound -/

noncomputable section
namespace NCBall

def upperSmoothRadius (δ Δ L : ℝ) : ℝ := min (δ / 2) (Δ / L)
def upperGoldsteinRadius (δ Δ L : ℝ) : ℝ := δ - upperSmoothRadius δ Δ L
def upperSmoothedGap (δ Δ L : ℝ) : ℝ := Δ + L * upperSmoothRadius δ Δ L

theorem upperSmoothRadius_pos {δ Δ L : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ) (hL : 0 < L) :
    0 < upperSmoothRadius δ Δ L := lt_min (by positivity) (div_pos hΔ hL)

theorem upperSmoothRadius_le_half (δ Δ L : ℝ) : upperSmoothRadius δ Δ L ≤ δ / 2 := min_le_left _ _

theorem upperGoldsteinRadius_lower (δ Δ L : ℝ) : δ / 2 ≤ upperGoldsteinRadius δ Δ L := by
  have h := upperSmoothRadius_le_half δ Δ L
  dsimp only [upperGoldsteinRadius]
  linarith

theorem upperGoldsteinRadius_pos {δ Δ L : ℝ} (hδ : 0 < δ) : 0 < upperGoldsteinRadius δ Δ L :=
  (by positivity : (0 : ℝ) < δ / 2).trans_le (upperGoldsteinRadius_lower δ Δ L)

theorem upper_radii_sum (δ Δ L : ℝ) : upperSmoothRadius δ Δ L + upperGoldsteinRadius δ Δ L = δ := by
  unfold upperGoldsteinRadius
  ring

theorem upperSmoothedGap_bounds {δ Δ L : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ) (hL : 0 < L) :
    0 < upperSmoothedGap δ Δ L ∧ upperSmoothedGap δ Δ L ≤ 2 * Δ := by
  have hp := upperSmoothRadius_pos hδ hΔ hL
  have hu : upperSmoothRadius δ Δ L * L ≤ Δ :=
    (le_div_iff₀ hL).mp (min_le_right _ _)
  constructor
  · exact add_pos hΔ (mul_pos hL hp)
  · dsimp only [upperSmoothedGap]
    nlinarith

theorem upper_radius_padding {δ Δ L ε R : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε) (hεL : ε ≤ L)
    (hR : 11 * Δ / ε ≤ R) : 10 * Δ / ε + upperSmoothRadius δ Δ L ≤ R := by
  have hL : 0 < L := hε.trans_le hεL
  have hρ : upperSmoothRadius δ Δ L ≤ Δ / ε := (min_le_right _ _).trans
    ((div_le_div_iff₀ hL hε).mpr (mul_le_mul_of_nonneg_left hεL hΔ.le))
  calc
    _ ≤ 10 * Δ / ε + Δ / ε := add_le_add_left hρ _
    _ = 11 * Δ / ε := by ring
    _ ≤ R := hR

theorem upper_smoothed_path_bound {δ Δ L ε : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hεL : ε ≤ L) :
    5 * upperSmoothedGap δ Δ L / ε ≤ 10 * Δ / ε := by
  have hb := (upperSmoothedGap_bounds hδ hΔ (hε.trans_le hεL)).2
  apply div_le_div_of_nonneg_right _ hε.le
  linarith

theorem upper_smoothing_ratio_bound {δ Δ L ε : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hεL : ε ≤ L) (n : ℕ) :
    (Real.sqrt (n + 1 : ℝ) * L) ^ 2 * upperSmoothedGap δ Δ L /
        (upperGoldsteinRadius δ Δ L * ε ^ 3) ≤
      4 * ((n + 1 : ℝ) * L ^ 2 * Δ / (δ * ε ^ 3)) := by
  have hν := upperGoldsteinRadius_pos (Δ := Δ) (L := L) hδ
  have hνδ := upperGoldsteinRadius_lower δ Δ L
  have hg := (upperSmoothedGap_bounds hδ hΔ (hε.trans_le hεL)).2
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ))]
  rw [show 4 * ((n + 1 : ℝ) * L ^ 2 * Δ / (δ * ε ^ 3)) =
    (4 * (n + 1 : ℝ) * L ^ 2 * Δ) / (δ * ε ^ 3) by ring]
  apply (div_le_div_iff₀ (mul_pos hν (pow_pos hε _)) (mul_pos hδ (pow_pos hε _))).mpr
  have hc : (n + 1 : ℝ) * L ^ 2 * upperSmoothedGap δ Δ L * δ ≤
      (4 * (n + 1 : ℝ) * L ^ 2 * Δ) * upperGoldsteinRadius δ Δ L := by
    calc
      _ ≤ (n + 1 : ℝ) * L ^ 2 * (2 * Δ) * δ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) hδ.le
      _ ≤ (n + 1 : ℝ) * L ^ 2 * (2 * Δ) * (2 * upperGoldsteinRadius δ Δ L) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  convert mul_le_mul_of_nonneg_right hc (le_of_lt (pow_pos hε 3)) using 1 <;> ring

theorem upper_scalar_call_bound {δ Δ L ε : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hεL : ε ≤ L) (n N : ℕ)
    (hN : (N : ℝ) ≤ 725 * (1 + (Real.sqrt (n + 1 : ℝ) * L) ^ 2 * upperSmoothedGap δ Δ L /
      (upperGoldsteinRadius δ Δ L * ε ^ 3))) :
    (2 * N : ℕ) ≤ 5800 * (1 + (n + 1 : ℝ) * L ^ 2 * Δ / (δ * ε ^ 3)) := by
  have hr := upper_smoothing_ratio_bound hδ hΔ hε hεL n
  push_cast
  linarith

theorem upper_variance_scale_ge {ε L : ℝ} (hε : 0 < ε) (hεL : ε ≤ L) (n : ℕ) :
    ε ≤ Real.sqrt (n + 1 : ℝ) * L := by
  have hs : 1 ≤ Real.sqrt (n + 1 : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
  have hL : 0 ≤ L := (hε.trans_le hεL).le
  exact hεL.trans (by nlinarith)

end NCBall
