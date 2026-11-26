import FreshGradientMinimax.CoreGate

/-! Sharp polynomial-times-exponential bounds from the tangent inequality for
exp. These avoid a separate maximization argument for each gate derivative. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open Real

theorem exp_one_rational_bounds : (27 / 10 : ℝ) ≤ exp 1 ∧ exp 1 ≤ 11 / 4 := by
  constructor <;> linarith [exp_one_gt_d9, exp_one_lt_d9]

theorem exp_half_le_five_thirds : exp (1 / 2 : ℝ) ≤ 5 / 3 := by
  have he : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by
    rw [sq, ← exp_add]
    norm_num
  nlinarith [exp_one_rational_bounds.2, exp_pos (1 / 2 : ℝ)]

theorem exp_neg_one_le : exp (-1 : ℝ) ≤ 10 / 27 := by
  rw [exp_neg, ← one_div]
  apply (div_le_iff₀ (exp_pos 1)).mpr
  nlinarith [exp_one_rational_bounds.1]

theorem power_exp_negative_le {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (hk : 0 < k) :
    x ^ k * exp (-x) ≤ (k : ℝ) ^ k * exp (-(k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have ht : x / k ≤ exp (x / k - 1) := by
    linarith [add_one_le_exp (x / k - 1)]
  have hp := pow_le_pow_left₀ (div_nonneg hx hk0.le) ht k
  have hmul := mul_le_mul_of_nonneg_left hp (pow_nonneg hk0.le k)
  have hl : (k : ℝ) ^ k * (x / k) ^ k = x ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hr : exp (x / k - 1) ^ k = exp (x - k) := by
    rw [← exp_nat_mul]
    congr 1
    field_simp
  rw [hl, hr] at hmul
  have hm := mul_le_mul_of_nonneg_right hmul (exp_pos (-x)).le
  have he : exp (x - k) * exp (-x) = exp (-(k : ℝ)) := by
    rw [← exp_add]
    congr 1
    ring
  simpa only [mul_assoc, he] using hm

theorem gaussian_cube_square_bound (v : ℝ) : v ^ 6 * exp (-(v ^ 2)) ≤ 27 * exp (-3 : ℝ) := by
  have h := power_exp_negative_le (sq_nonneg v) 3 (by norm_num)
  norm_num only [Nat.cast_ofNat] at h
  convert h using 1
  ring

theorem gaussian_fourth_bound (v : ℝ) : v ^ 4 * exp (-(v ^ 2) / 2) ≤ 1600 / 729 := by
  have h := power_exp_negative_le (by positivity : 0 ≤ v ^ 2 / 2) 2 (by norm_num)
  have he : exp (-2 : ℝ) ≤ (10 / 27 : ℝ) ^ 2 := by
    have hp := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le exp_neg_one_le 2
    have hid : exp (-2 : ℝ) = exp (-1 : ℝ) ^ 2 := by
      simpa using exp_nat_mul (-1 : ℝ) 2
    rw [hid]
    exact hp
  norm_num only [Nat.cast_ofNat] at h
  have hx : exp (-(v ^ 2 / 2)) = exp (-(v ^ 2) / 2) := by congr 1; ring
  rw [hx] at h
  nlinarith

theorem gaussian_sixth_bound (v : ℝ) : v ^ 6 * exp (-(v ^ 2) / 2) ≤ 8000 / 729 := by
  have h := power_exp_negative_le (by positivity : 0 ≤ v ^ 2 / 2) 3 (by norm_num)
  have he : exp (-3 : ℝ) ≤ (10 / 27 : ℝ) ^ 3 := by
    have hp := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le exp_neg_one_le 3
    have hid : exp (-3 : ℝ) = exp (-1 : ℝ) ^ 3 := by
      simpa using exp_nat_mul (-1 : ℝ) 3
    rw [hid]
    exact hp
  norm_num only [Nat.cast_ofNat] at h
  have hx : exp (-(v ^ 2 / 2)) = exp (-(v ^ 2) / 2) := by congr 1; ring
  rw [hx] at h
  nlinarith

theorem gaussian_cube_derivative_bound (v : ℝ) :
    |2 * exp (1 / 2 : ℝ) * v ^ 3 * exp (-(v ^ 2) / 2)| ≤ 4 := by
  have h := gaussian_cube_square_bound v
  have he : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by
    rw [sq, ← exp_add]
    norm_num
  have hd : exp (-(v ^ 2) / 2) ^ 2 = exp (-(v ^ 2)) := by
    rw [sq, ← exp_add]
    congr 1
    ring
  have hn : exp 1 * exp (-3 : ℝ) = exp (-2 : ℝ) := by
    rw [← exp_add]
    norm_num
  have hi : exp (-2 : ℝ) ≤ (10 / 27 : ℝ) ^ 2 := by
    have hp := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le exp_neg_one_le 2
    simpa only [← exp_nat_mul, Nat.cast_ofNat, mul_neg, mul_one] using hp
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 4 * exp 1 by positivity)
  have hs : (2 * exp (1 / 2 : ℝ) * v ^ 3 * exp (-(v ^ 2) / 2)) ^ 2 =
      4 * exp 1 * (v ^ 6 * exp (-(v ^ 2))) := by
    simp only [mul_pow, he, hd, ← pow_mul]
    ring
  have hright : 4 * exp 1 * (27 * exp (-3 : ℝ)) = 108 * exp (-2 : ℝ) := by
    calc
      _ = 108 * (exp 1 * exp (-3 : ℝ)) := by ring
      _ = _ := by rw [hn]
  rw [← hs, hright] at hm
  nlinarith [sq_abs (2 * exp (1 / 2 : ℝ) * v ^ 3 * exp (-(v ^ 2) / 2)),
    abs_nonneg (2 * exp (1 / 2 : ℝ) * v ^ 3 * exp (-(v ^ 2) / 2))]

theorem gaussian_root_second_bound (v : ℝ) :
    |4 * exp (1 / 2 : ℝ) * (v ^ 6 - 3 * v ^ 4) * exp (-(v ^ 2) / 2)| ≤ 120 := by
  have hc : 0 ≤ 4 * exp (1 / 2 : ℝ) := by positivity
  have he : 0 ≤ exp (-(v ^ 2) / 2) := (exp_pos _).le
  have hpoly : |v ^ 6 - 3 * v ^ 4| ≤ v ^ 6 + 3 * v ^ 4 := by
    apply abs_le.mpr
    constructor <;> nlinarith [show 0 ≤ v ^ 6 by positivity, show 0 ≤ v ^ 4 by positivity]
  rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg he]
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hc) he
  have hsum : (v ^ 6 + 3 * v ^ 4) * exp (-(v ^ 2) / 2) ≤ 12800 / 729 := by
    nlinarith [gaussian_fourth_bound v, gaussian_sixth_bound v]
  have hsum0 : 0 ≤ (v ^ 6 + 3 * v ^ 4) * exp (-(v ^ 2) / 2) := by positivity
  have hm := mul_le_mul (show 4 * exp (1 / 2 : ℝ) ≤ 20 / 3 by linarith [exp_half_le_five_thirds])
    hsum hsum0 (by norm_num : (0 : ℝ) ≤ 20 / 3)
  nlinarith only [hp, hm]

end FreshGradientMinimax
