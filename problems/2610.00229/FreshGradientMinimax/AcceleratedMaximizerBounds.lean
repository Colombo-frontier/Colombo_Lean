import FreshGradientMinimax.AcceleratedUncapped
import FreshGradientMinimax.PrimalParameters

/-! Actual multi-chain optimizer bounds at the original E.2 threshold and
radius, including all rounding-free finite-dimensional edge cases. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def acceleratedThreshold (n k : ℕ) : ℝ :=
  primalRidgeConstant / (10 ^ 8 * (n + 2 : ℕ) ^ 2 * Real.sqrt (k * (n + 3) : ℕ))

def acceleratedDualRadius (n k : ℕ) : ℝ := 1000 * (n + 2 : ℕ) * Real.sqrt (k + 1 : ℕ)

theorem acceleratedThreshold_pos (n : ℕ) {k : ℕ} (hk : 0 < k) : 0 < acceleratedThreshold n k := by
  have hM : 0 < ((k * (n + 3) : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hk (by omega))
  exact div_pos primalRidgeConstant_pos (by positivity)

theorem acceleratedDualRadius_pos (n k : ℕ) : 0 < acceleratedDualRadius n k := by
  unfold acceleratedDualRadius
  positivity

theorem acceleratedQuadraticMaximizer_norm {n k : ℕ} (hn : 10 ≤ n + 2) (u : Euclid (k * 2 + 1)) :
    ‖acceleratedQuadraticMaximizer n k u‖ ≤ 42 * (n + 2 : ℕ) * Real.sqrt (k + 1 : ℕ) := by
  have h := euclidJoin_norm_bound (by positivity : (0 : ℝ) ≤ 42 * (n + 2 : ℕ))
    (fun i : Fin k => robinQuadraticOptimizer n (clipVector 2 u (interleavedX i)) (clipVector 2 u (interleavedZ i) / 2))
    (fun i => robin_optimizer_norm_bound hn (clip_two_coordinate _ _) (clip_two_half_coordinate _ _))
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.le_succ k))) (by positivity))

theorem acceleratedHuberMaximizer_displacement {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) :
    ‖acceleratedHuberMaximizer n k δ u hδ - acceleratedQuadraticMaximizer n k u‖ ≤
      2 * (n + 2 : ℕ) ^ 2 * δ * Real.sqrt (k * (n + 3) : ℕ) := by
  unfold acceleratedHuberMaximizer acceleratedQuadraticMaximizer
  rw [euclidJoin_sub]
  have h := euclidJoin_norm_bound (by positivity : 0 ≤ 2 * (n + 2 : ℕ) ^ 2 * δ * Real.sqrt (n + 3 : ℕ))
    (fun i : Fin k => robinHuberMaximizer n δ (clipVector 2 u (interleavedX i)) (clipVector 2 u (interleavedZ i) / 2) hδ -
      robinQuadraticOptimizer n (clipVector 2 u (interleavedX i)) (clipVector 2 u (interleavedZ i) / 2))
    (fun i => robinHuberMaximizer_displacement hn hδ (clip_two_coordinate _ _) (clip_two_half_coordinate _ _))
  convert h using 1
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg k)]
  ring

theorem acceleratedThreshold_displacement_scale (n : ℕ) {k : ℕ} (hk : 0 < k) :
    2 * (n + 2 : ℕ) ^ 2 * acceleratedThreshold n k * Real.sqrt (k * (n + 3) : ℕ) =
      2 * primalRidgeConstant / 10 ^ 8 := by
  have hN : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hM : Real.sqrt (k * (n + 3) : ℕ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.mul_pos hk (by omega)))).ne'
  unfold acceleratedThreshold
  field_simp
  ring

theorem accelerated_dimension_scale_ge_one (n k : ℕ) :
    (1 : ℝ) ≤ (n + 2 : ℕ) * Real.sqrt (k + 1 : ℕ) := by
  have hN : (1 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hT : (1 : ℝ) ≤ Real.sqrt (k + 1 : ℕ) := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ k + 1 by omega))
  nlinarith only [hN, hT, mul_le_mul hN hT (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ (n + 2 : ℕ))]

theorem acceleratedHuberMaximizer_threshold_norm {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k)
    (u : Euclid (k * 2 + 1)) :
    ‖acceleratedHuberMaximizer n k (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le‖ ≤
      43 * (n + 2 : ℕ) * Real.sqrt (k + 1 : ℕ) := by
  have hd := acceleratedHuberMaximizer_displacement hn (acceleratedThreshold_pos n hk).le u
  rw [acceleratedThreshold_displacement_scale n hk] at hd
  have hd1 : ‖acceleratedHuberMaximizer n k (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le -
      acceleratedQuadraticMaximizer n k u‖ ≤ 1 := by
    nlinarith only [hd, primalRidgeConstant_le_one]
  have hsum := norm_add_le
    (acceleratedHuberMaximizer n k (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le - acceleratedQuadraticMaximizer n k u)
    (acceleratedQuadraticMaximizer n k u)
  rw [sub_add_cancel] at hsum
  nlinarith only [hsum, hd1, acceleratedQuadraticMaximizer_norm hn u, accelerated_dimension_scale_ge_one n k]

theorem acceleratedHuberMaximizer_in_core {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k)
    (u : Euclid (k * 2 + 1)) :
    ‖acceleratedHuberMaximizer n k (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le‖ <
      acceleratedDualRadius n k / 2 := by
  have h := acceleratedHuberMaximizer_threshold_norm hn hk u
  have hp := accelerated_dimension_scale_ge_one n k
  unfold acceleratedDualRadius
  nlinarith only [h, hp]

end FreshGradientMinimax
