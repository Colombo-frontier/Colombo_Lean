import FreshGradientMinimax.ClipSquare
import FreshGradientMinimax.Calculus
import FreshGradientMinimax.RealCoordinate

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem clipSquare_taylor {R : ℝ} (hR : 0 < R) (x y : ℝ) :
    |clipSquare R y - clipSquare R x - clipSquareSlope R x * (y - x)| ≤
      (13 / 8) * (y - x) ^ 2 := by
  have h := smooth_taylor_remainder
    (fun t => scalar_hasFDerivAt (clipSquare_derivative hR t))
    (fun s t => show ‖clipSquareSlope R s - clipSquareSlope R t‖ ≤ (13 / 4) * ‖s - t‖ by
      simpa only [Real.norm_eq_abs] using clipSquareSlope_lipschitz hR s t) x (y - x)
  have he : x + (y - x) = y := by ring
  simpa only [he, RCLike.inner_apply', conj_trivial,
    Real.norm_eq_abs, sq_abs, show (13 / 4 : ℝ) / 2 = 13 / 8 by norm_num] using h

end FreshGradientMinimax
