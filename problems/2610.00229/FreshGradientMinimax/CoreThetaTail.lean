import FreshGradientMinimax.GaussianPowerBounds

/-! A direct finite-interval lower bound for the Gaussian tail. The loose
constant 9 is sufficient for the original square-root derivative bounds. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open Real MeasureTheory Set

theorem coreTheta_monotone : Monotone coreTheta := by
  intro a b hab
  have h := intervalIntegral.integral_nonneg (μ := volume) hab (fun s _ => (coreDensity_pos s).le)
  rw [← coreTheta_sub] at h
  linarith

theorem exp_two_le_nine : exp (2 : ℝ) ≤ 9 := by
  have he : exp 1 ≤ 3 := by linarith [exp_one_rational_bounds.2]
  have hp := pow_le_pow_left₀ (exp_pos 1).le he 2
  have hid : exp (2 : ℝ) = exp 1 ^ 2 := by rw [sq, ← exp_add]; norm_num
  rw [hid]
  norm_num at hp ⊢
  exact hp

theorem coreDensity_tail_interval {r s : ℝ} (hr : 1 ≤ r)
    (hs : s ∈ Icc (-r - r⁻¹) (-r)) : coreDensity r / 9 ≤ coreDensity s := by
  have hr0 : 0 < r := by linarith
  have hi0 : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have hi1 : r⁻¹ ≤ 1 := (inv_le_one₀ hr0).mpr hr
  have hi2 : (r⁻¹) ^ 2 ≤ 1 := by nlinarith [mul_self_le_mul_self hi0 hi1]
  have hri : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
  have hs0 : 0 ≤ -s := by linarith [hs.2]
  have hsr : -s ≤ r + r⁻¹ := by linarith [hs.1]
  have hsq : s ^ 2 ≤ r ^ 2 + 3 := by
    nlinarith [mul_self_le_mul_self hs0 hsr]
  have he : coreDensity r ≤ exp 2 * coreDensity s := by
    unfold coreDensity
    rw [← exp_add]
    apply exp_le_exp.mpr
    linarith
  have hm := mul_le_mul_of_nonneg_right exp_two_le_nine (coreDensity_pos s).le
  linarith

theorem coreTheta_tail_lower {r : ℝ} (hr : 1 ≤ r) :
    coreDensity r / (9 * r) ≤ coreTheta (-r) := by
  have hr0 : 0 < r := by linarith
  have hab : -r - r⁻¹ ≤ -r := sub_le_self _ (inv_nonneg.mpr hr0.le)
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (continuous_const.intervalIntegrable (-r - r⁻¹) (-r))
    (coreDensity_continuous.intervalIntegrable (-r - r⁻¹) (-r))
    (fun s hs => coreDensity_tail_interval hr hs)
  rw [intervalIntegral.integral_const, ← coreTheta_sub] at hi
  have he : (-r - (-r - r⁻¹)) • (coreDensity r / 9) = coreDensity r / (9 * r) := by
    simp only [smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at hi
  linarith [coreTheta_pos (-r - r⁻¹)]

theorem coreDensity_one_lower : (1 / 3 : ℝ) ≤ coreDensity 1 := by
  have hi : exp (1 / 2 : ℝ) * coreDensity 1 = 1 := by
    unfold coreDensity
    rw [← exp_add]
    norm_num
  have h := mul_le_mul_of_nonneg_right exp_half_le_five_thirds (coreDensity_pos 1).le
  nlinarith

theorem coreTheta_lower_above_neg_one {t : ℝ} (ht : -1 ≤ t) : (1 / 27 : ℝ) ≤ coreTheta t := by
  have h := coreTheta_tail_lower (r := 1) (by norm_num)
  have hm := coreTheta_monotone ht
  norm_num only [mul_one, neg_pos] at h
  linarith [coreDensity_one_lower]

theorem coreDensity_abs_mul_le_one (t : ℝ) : |t| * coreDensity t ≤ 1 := by
  have h : |t| ≤ exp (t ^ 2 / 2) := by
    nlinarith [add_one_le_exp (t ^ 2 / 2), sq_nonneg (|t| - 1), sq_abs t]
  have hm := mul_le_mul_of_nonneg_right h (coreDensity_pos t).le
  have he : exp (t ^ 2 / 2) * coreDensity t = 1 := by
    unfold coreDensity
    rw [← exp_add]
    have : t ^ 2 / 2 + -(t ^ 2) / 2 = 0 := by ring
    rw [this, exp_zero]
  rwa [he] at hm

theorem coreDensity_cubic_tail {r : ℝ} (hr : 1 ≤ r) : r ^ 3 * coreDensity r ≤ 8 := by
  have hr0 : 0 < r := by linarith
  have he := Real.pow_div_factorial_le_exp (r ^ 2 / 2) (by positivity) 2
  have hm := mul_le_mul_of_nonneg_right he (coreDensity_pos r).le
  have hi : exp (r ^ 2 / 2) * coreDensity r = 1 := by
    unfold coreDensity
    rw [← exp_add]
    have : r ^ 2 / 2 + -(r ^ 2) / 2 = 0 := by ring
    rw [this, exp_zero]
  rw [hi] at hm
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hm
  have hpow : r ^ 3 ≤ r ^ 4 := by nlinarith [pow_nonneg hr0.le 3]
  have hh := mul_le_mul_of_nonneg_right hpow (coreDensity_pos r).le
  nlinarith only [hm, hh]

end FreshGradientMinimax
