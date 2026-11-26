import FreshGradientMinimax.UnitClipBounds

/-! The radius-R clip of Appendix A.1 with every assertion in (15). -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def smoothClip (R t : ℝ) : ℝ := R * unitClip (t / R)
def smoothClipSlope (R t : ℝ) : ℝ := unitClipSlope (t / R)
def smoothClipCurve (R t : ℝ) : ℝ := unitClipCurve (t / R) / R

theorem smoothClip_derivative {R : ℝ} (hR : 0 < R) (t : ℝ) :
    HasDerivAt (smoothClip R) (smoothClipSlope R t) t := by
  apply (((unitClip_derivative (t / R)).comp t
    ((hasDerivAt_id t).div_const R)).const_mul R).congr_deriv
  simp only [smoothClipSlope]
  field_simp

theorem smoothClipSlope_derivative {R : ℝ} (_hR : 0 < R) (t : ℝ) :
    HasDerivAt (smoothClipSlope R) (smoothClipCurve R t) t := by
  apply ((unitClipSlope_derivative (t / R)).comp t
    ((hasDerivAt_id t).div_const R)).congr_deriv
  simp only [smoothClipCurve, mul_one_div]

theorem smoothClip_contDiff (R : ℝ) : ContDiff ℝ 2 (smoothClip R) :=
  contDiff_const.mul (unitClip_contDiff.comp (contDiff_id.div_const R))

theorem smoothClip_odd (R t : ℝ) : smoothClip R (-t) = -smoothClip R t := by
  simp only [smoothClip, neg_div, unitClip_odd, mul_neg]

theorem smoothClip_identity {R t : ℝ} (hR : 0 < R) (ht : |t| ≤ R) :
    smoothClip R t = t := by
  have h : |t / R| ≤ 1 := by
    rw [abs_div, abs_of_pos hR]
    exact (div_le_one hR).mpr ht
  rw [smoothClip, unitClip_identity h]
  field_simp

theorem smoothClipSlope_identity {R t : ℝ} (hR : 0 < R) (ht : |t| ≤ R) :
    smoothClipSlope R t = 1 := by
  apply unitClipSlope_identity
  rw [abs_div, abs_of_pos hR]
  exact (div_le_one hR).mpr ht

theorem smoothClipCurve_identity {R t : ℝ} (hR : 0 < R) (ht : |t| ≤ R) :
    smoothClipCurve R t = 0 := by
  have h : |t / R| ≤ 1 := by
    rw [abs_div, abs_of_pos hR]
    exact (div_le_one hR).mpr ht
  simp only [smoothClipCurve, unitClipCurve_identity h, zero_div]

theorem smoothClip_bound {R : ℝ} (hR : 0 < R) (t : ℝ) :
    |smoothClip R t| ≤ 3 * R / 2 := by
  rw [smoothClip, abs_mul, abs_of_pos hR]
  have h := mul_le_mul_of_nonneg_left (unitClip_bound (t / R)) hR.le
  linarith

theorem smoothClip_le_abs {R : ℝ} (hR : 0 < R) (t : ℝ) :
    |smoothClip R t| ≤ |t| := by
  rw [smoothClip, abs_mul, abs_of_pos hR]
  have h := mul_le_mul_of_nonneg_left (unitClip_le_abs (t / R)) hR.le
  rw [abs_div, abs_of_pos hR] at h
  have he : R * (|t| / R) = |t| := by field_simp
  rwa [he] at h

theorem smoothClipSlope_bounds (R t : ℝ) :
    0 ≤ smoothClipSlope R t ∧ smoothClipSlope R t ≤ 1 := unitClipSlope_bounds _

theorem smoothClipCurve_bound {R : ℝ} (hR : 0 < R) (t : ℝ) :
    |smoothClipCurve R t| ≤ 3 / (2 * R) := by
  rw [smoothClipCurve, abs_div, abs_of_pos hR]
  have h := div_le_div_of_nonneg_right (unitClipCurve_bound (t / R)) hR.le
  convert h using 1
  ring

theorem smoothClip_lipschitz {R : ℝ} (hR : 0 < R) (x y : ℝ) :
    |smoothClip R x - smoothClip R y| ≤ |x - y| := by
  have h := mul_le_mul_of_nonneg_left (unitClip_lipschitz (x / R) (y / R)) hR.le
  rw [← sub_div, abs_div, abs_of_pos hR] at h
  rw [smoothClip, smoothClip, ← mul_sub, abs_mul, abs_of_pos hR]
  have he : R * (|x - y| / R) = |x - y| := by field_simp
  rwa [he] at h

end FreshGradientMinimax
