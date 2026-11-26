import FreshGradientMinimax.SmoothClip

/-! The globally smooth bounded-gradient perturbation used in Appendix D. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def clipSquare (R t : ℝ) : ℝ := (smoothClip R t) ^ 2 / 2
def clipSquareSlope (R t : ℝ) : ℝ := smoothClip R t * smoothClipSlope R t
def clipSquareCurve (R t : ℝ) : ℝ := (smoothClipSlope R t) ^ 2 +
  smoothClip R t * smoothClipCurve R t

theorem clipSquare_derivative {R : ℝ} (hR : 0 < R) (t : ℝ) :
    HasDerivAt (clipSquare R) (clipSquareSlope R t) t := by
  apply (((smoothClip_derivative hR t).pow 2).div_const 2).congr_deriv
  simp only [clipSquareSlope, pow_one]
  ring

theorem clipSquareSlope_derivative {R : ℝ} (hR : 0 < R) (t : ℝ) :
    HasDerivAt (clipSquareSlope R) (clipSquareCurve R t) t := by
  apply ((smoothClip_derivative hR t).mul (smoothClipSlope_derivative hR t)).congr_deriv
  simp only [clipSquareCurve]
  ring

theorem clipSquare_contDiff (R : ℝ) : ContDiff ℝ 2 (clipSquare R) :=
  ((smoothClip_contDiff R).pow 2).div_const 2

theorem clipSquare_nonneg (R t : ℝ) : 0 ≤ clipSquare R t := by
  unfold clipSquare; positivity

theorem clipSquare_identity {R t : ℝ} (hR : 0 < R) (ht : |t| ≤ R) :
    clipSquare R t = t ^ 2 / 2 := by
  simp only [clipSquare, smoothClip_identity hR ht]

theorem clipSquareSlope_identity {R t : ℝ} (hR : 0 < R) (ht : |t| ≤ R) :
    clipSquareSlope R t = t := by
  simp only [clipSquareSlope, smoothClip_identity hR ht,
    smoothClipSlope_identity hR ht, mul_one]

theorem clipSquareCurve_identity {R t : ℝ} (hR : 0 < R) (ht : |t| ≤ R) :
    clipSquareCurve R t = 1 := by
  simp only [clipSquareCurve, smoothClipSlope_identity hR ht,
    smoothClipCurve_identity hR ht, one_pow, mul_zero, add_zero]

theorem clipSquareSlope_bound {R : ℝ} (hR : 0 < R) (t : ℝ) :
    |clipSquareSlope R t| ≤ 3 * R / 2 := by
  rw [clipSquareSlope, abs_mul,
    abs_of_nonneg (smoothClipSlope_bounds R t).1]
  calc
    _ ≤ |smoothClip R t| * 1 := mul_le_mul_of_nonneg_left
      (smoothClipSlope_bounds R t).2 (abs_nonneg _)
    _ ≤ 3 * R / 2 := by simpa only [mul_one] using smoothClip_bound hR t

theorem clipSquareSlope_le_abs {R : ℝ} (hR : 0 < R) (t : ℝ) :
    |clipSquareSlope R t| ≤ |t| := by
  rw [clipSquareSlope, abs_mul,
    abs_of_nonneg (smoothClipSlope_bounds R t).1]
  calc
    _ ≤ |smoothClip R t| * 1 := mul_le_mul_of_nonneg_left
      (smoothClipSlope_bounds R t).2 (abs_nonneg _)
    _ ≤ |t| := by simpa only [mul_one] using smoothClip_le_abs hR t

theorem clipSquareCurve_bound {R : ℝ} (hR : 0 < R) (t : ℝ) :
    |clipSquareCurve R t| ≤ 13 / 4 := by
  have hs := smoothClipSlope_bounds R t
  have hss : (smoothClipSlope R t) ^ 2 ≤ 1 := by nlinarith
  have hp := mul_le_mul (smoothClip_bound hR t) (smoothClipCurve_bound hR t)
    (abs_nonneg _) (show 0 ≤ 3 * R / 2 by positivity)
  have he : 3 * R / 2 * (3 / (2 * R)) = (9 : ℝ) / 4 := by field_simp; ring
  rw [he, ← abs_mul] at hp
  have h := abs_add ((smoothClipSlope R t) ^ 2) (smoothClip R t * smoothClipCurve R t)
  rw [abs_of_nonneg (sq_nonneg (smoothClipSlope R t))] at h
  unfold clipSquareCurve
  linarith

theorem clipSquareSlope_lipschitz {R : ℝ} (hR : 0 < R) (x y : ℝ) :
    |clipSquareSlope R x - clipSquareSlope R y| ≤ (13 / 4) * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (C := 13 / 4) (fun t _ => (clipSquareSlope_derivative hR t).hasDerivWithinAt)
    (fun t _ => show ‖clipSquareCurve R t‖ ≤ 13 / 4 by
      simpa only [Real.norm_eq_abs] using clipSquareCurve_bound hR t)
    (convex_univ) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

theorem clipSquare_le_square {R : ℝ} (hR : 0 < R) (t : ℝ) :
    clipSquare R t ≤ t ^ 2 / 2 := by
  have h := (sq_le_sq).mpr (smoothClip_le_abs hR t)
  unfold clipSquare
  linarith

end FreshGradientMinimax
