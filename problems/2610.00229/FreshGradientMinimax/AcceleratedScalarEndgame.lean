import FreshGradientMinimax.AcceleratedPrimalGradient
import FreshGradientMinimax.PrimalParameters

/-! The scalar robust endgame, including both clip transition and saturation.
Only the already established weaker bound p >= -6 is needed. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem smoothClip_monotone {R : ℝ} (hR : 0 < R) : Monotone (smoothClip R) :=
  monotone_of_hasDerivAt_nonneg (smoothClip_derivative hR) (fun t => (smoothClipSlope_bounds R t).1)

theorem smoothClip_two_ge_one {v : ℝ} (hv : 1 ≤ v) : 1 ≤ smoothClip 2 v := by
  have h := smoothClip_monotone (by norm_num : (0 : ℝ) < 2) hv
  rwa [smoothClip_identity (by norm_num : (0 : ℝ) < 2) (by norm_num : |(1 : ℝ)| ≤ 2)] at h

theorem smoothClip_two_le_neg_one {v : ℝ} (hv : v ≤ -1) : smoothClip 2 v ≤ -1 := by
  have h := smoothClip_monotone (by norm_num : (0 : ℝ) < 2) hv
  rwa [smoothClip_identity (by norm_num : (0 : ℝ) < 2) (by norm_num : |(-1 : ℝ)| ≤ 2)] at h

theorem smoothClip_two_abs_ge_one {v : ℝ} (hv : 1 ≤ |v|) : 1 ≤ |smoothClip 2 v| := by
  rcases le_abs.mp hv with h | h
  · exact (smoothClip_two_ge_one h).trans (le_abs_self _)
  · have hh := smoothClip_two_le_neg_one (by linarith only [h])
    exact le_trans (by linarith only [hh]) (neg_le_abs _)

theorem accelerated_scaled_error_bound {a e : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (he : |e| ≤ primalRidgeConstant / 100) : |a * e| ≤ primalRidgeConstant / 100 := by
  rw [abs_mul, abs_of_nonneg ha]
  simpa only [one_mul] using mul_le_mul ha1 he (abs_nonneg e) (by norm_num : (0 : ℝ) ≤ 1)

theorem accelerated_scalar_endgame {a b v z p q ev ez gv gz : ℝ}
    (ha : 4 / 5 ≤ a) (ha1 : a ≤ 1)
    (hb : (9 / 10) * primalRidgeConstant ≤ b) (hb1 : b ≤ (13 / 10) * primalRidgeConstant)
    (hz : |z| < 1) (hp : -6 ≤ p) (hp0 : p ≤ 0) (hq : q ≤ 0)
    (hps : |v| < 1 → p ≤ -primalBarrierConstant)
    (hev : |ev| ≤ primalRidgeConstant / 100) (hez : |ez| ≤ primalRidgeConstant / 100)
    (hgv : gv = a * (smoothClipSlope 2 v * (p + 12 * (smoothClip 2 v - z / 2)) + ev) + b * v)
    (hgz : gz = a * (q - 6 * (smoothClip 2 v - z / 2) + ez) + b * z) :
    primalRidgeConstant / 2 ≤ |gv| ∨ primalRidgeConstant / 2 ≤ |gz| := by
  have ha0 : 0 ≤ a := by linarith only [ha]
  have hb0 : 0 ≤ b := by nlinarith only [hb, primalRidgeConstant_pos]
  have hev' := abs_le.mp (accelerated_scaled_error_bound ha0 ha1 hev)
  have hez' := abs_le.mp (accelerated_scaled_error_bound ha0 ha1 hez)
  have hz' := abs_lt.mp hz
  have hs := (smoothClipSlope_bounds 2 v).1
  by_cases hv : |v| < 1
  · have hv' := abs_lt.mp hv
    have hcv := smoothClip_identity (by norm_num : (0 : ℝ) < 2) (show |v| ≤ 2 by linarith only [hv])
    have hsv := smoothClipSlope_identity (by norm_num : (0 : ℝ) < 2) (show |v| ≤ 2 by linarith only [hv])
    rw [hcv, hsv, one_mul] at hgv
    rw [hcv] at hgz
    have hp' := mul_le_mul_of_nonneg_left (hps hv) ha0
    have hq' := mul_nonpos_of_nonneg_of_nonpos ha0 hq
    have hb' : b * (v + 2 * z) ≤ 3 * b := by
      nlinarith only [mul_le_mul_of_nonneg_left (show v + 2 * z ≤ 3 by linarith only [hv'.2, hz'.2]) hb0]
    have ha' := mul_le_mul_of_nonneg_right ha primalBarrierConstant_pos.le
    have hsum : gv + 2 * gz ≤ -(4 / 5) * primalBarrierConstant + (393 / 100) * primalRidgeConstant := by
      nlinarith only [hgv, hgz, hp', hq', hb', ha', hb1, hev'.2, hez'.2]
    by_cases hg : primalRidgeConstant / 2 ≤ |gv|
    · exact Or.inl hg
    · right
      by_contra hg'
      have h1 := neg_le_abs gv
      have h2 := neg_le_abs gz
      have hη : primalRidgeConstant = primalBarrierConstant / 100 := rfl
      nlinarith only [hsum, lt_of_not_ge hg, lt_of_not_ge hg', h1, h2, hη, primalBarrierConstant_pos]
  · have hv' : 1 ≤ |v| := le_of_not_gt hv
    rcases le_abs.mp hv' with hvp | hvn
    · have hc := smoothClip_two_ge_one hvp
      have ht : 0 ≤ p + 12 * (smoothClip 2 v - z / 2) := by linarith only [hp, hc, hz'.2]
      have hst := mul_nonneg ha0 (mul_nonneg hs ht)
      have hb' : b ≤ b * v := by nlinarith only [mul_nonneg hb0 (sub_nonneg.mpr hvp)]
      left
      exact le_trans (by nlinarith only [hgv, hst, hb', hb, hev'.1, primalRidgeConstant_pos]) (le_abs_self gv)
    · have hvn' : v ≤ -1 := by linarith only [hvn]
      have hc := smoothClip_two_le_neg_one hvn'
      have ht : p + 12 * (smoothClip 2 v - z / 2) ≤ 0 := by linarith only [hp0, hc, hz'.1]
      have hst := mul_nonpos_of_nonneg_of_nonpos ha0 (mul_nonpos_of_nonneg_of_nonpos hs ht)
      have hb' : b * v ≤ -b := by nlinarith only [mul_nonpos_of_nonneg_of_nonpos hb0 (show v + 1 ≤ 0 by linarith)]
      left
      exact le_trans (by nlinarith only [hgv, hst, hb', hb, hev'.2, primalRidgeConstant_pos]) (neg_le_abs gv)

end FreshGradientMinimax
