import NCBall.ChargeParameters
import NCBall.ChainProbabilityScale

/-! # Removing the implicit logarithm of the dimension from the size condition -/

noncomputable section
namespace NCBall

theorem log_two_add_lower {A : ℝ} (hA : 0 ≤ A) : 1 / 2 ≤ Real.log (2 + A) := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 + A)
  norm_num at h2
  linarith

theorem uniform_log_dimension {n : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hn : 12800 * Real.log (2 + A) ≤ n) :
    40 * Real.log (2 + (n : ℝ) * A) ≤ n := by
  have hlower := log_two_add_lower hA
  have hnlarge : (6400 : ℝ) ≤ n := by linarith
  have hnp : (0 : ℝ) < n := by linarith
  have hscale := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) / 80 by positivity)
  have h80 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 80)
  rw [Real.log_div (ne_of_gt hnp) (by norm_num)] at hscale
  have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) / 80 + 79 := by linarith
  have hle : 2 + (n : ℝ) * A ≤ (n : ℝ) * (2 + A) := by nlinarith
  have hl := Real.log_le_log (show 0 < 2 + (n : ℝ) * A by positivity) hle
  rw [Real.log_mul (ne_of_gt hnp) (by positivity : 2 + A ≠ 0)] at hl
  linarith

theorem dimension_good_log {M q₀ n : ℕ} (hq : 0 < q₀)
    (hlog : 40 * Real.log (2 + (M * q₀ : ℕ)) ≤ n) :
    2 * Real.log (8 * ((M : ℝ) + 1)) ≤ n := by
  have hMq : (M : ℝ) ≤ (M * q₀ : ℕ) := by exact_mod_cast Nat.le_mul_of_pos_right M hq
  have hlower := log_two_add_lower (Nat.cast_nonneg (α := ℝ) (M * q₀))
  have hl := Real.log_le_log (by positivity : 0 < (M : ℝ) + 1)
    (show (M : ℝ) + 1 ≤ 2 + (M * q₀ : ℕ) by linarith)
  have h8 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity : (M : ℝ) + 1 ≠ 0)]
  linarith

theorem calibrated_product_upper {n : ℕ} {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ) :
    (calibratedDepth (4 * η) H Δ * calibratedCharges n (4 * η) L : ℕ) ≤
      (n : ℝ) * (H * Δ * L ^ 2 / η ^ 4) := by
  have hC := bumpConstant_ge_one
  have hCp := bumpConstant_pos
  have hM : (calibratedDepth (4 * η) H Δ : ℝ) ≤ H * Δ / (100 * bumpConstant * (4 * η) ^ 2) :=
    Nat.floor_le (by positivity)
  have hq := calibratedCharges_cap n (4 * η) L
  have hp := mul_le_mul hM hq (Nat.cast_nonneg _) (by positivity)
  have he : (H * Δ / (100 * bumpConstant * (4 * η) ^ 2)) *
      ((n : ℝ) * (L / (4 * η)) ^ 2 / 16) =
      ((n : ℝ) * (H * Δ * L ^ 2 / η ^ 4)) / (409600 * bumpConstant) := by
    field_simp
    ring
  rw [he] at hp
  have hx : 0 ≤ (n : ℝ) * (H * Δ * L ^ 2 / η ^ 4) := by positivity
  have hden : 1 ≤ 409600 * bumpConstant := by linarith
  have hb := div_le_self hx hden
  push_cast
  exact hp.trans hb

theorem calibrated_dimension_condition {n : ℕ} {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ)
    (hlog : 12800 * Real.log (2 + H * Δ * L ^ 2 / η ^ 4) ≤ n) :
    40 * Real.log (2 + (calibratedDepth (4 * η) H Δ * calibratedCharges n (4 * η) L : ℕ)) ≤ n := by
  have ha : 0 ≤ H * Δ * L ^ 2 / η ^ 4 := by positivity
  have hu := calibrated_product_upper (n := n) hη hH hΔ (L := L)
  have hl := Real.log_le_log
    (by positivity : (0 : ℝ) < 2 + ((calibratedDepth (4 * η) H Δ * calibratedCharges n (4 * η) L : ℕ) : ℝ))
    (add_le_add_left hu 2)
  exact (mul_le_mul_of_nonneg_left hl (by norm_num)).trans (uniform_log_dimension ha hlog)

end NCBall
