import Nonsmooth.VectorCoordinateMoments
import Nonsmooth.CoordinateHessianGrowth
import Nonsmooth.StrongPotentialRawMoment

open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coordinate_slice_raw_second_growth (V dx : E → ℝ → ℝ)
    (hcd : ∀ t, Continuous (dx t))
    (hd : ∀ t x, HasDerivAt (V t) (dx t x) x)
    (hm : ∀ t, Monotone (fun x => dx t x - 1 * x))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, |dx t 0| ≤ C * (1 + ‖t‖)) (t : E) :
    (∫ x : ℝ, x ^ 2 ∂realDensityLaw (fun x => Real.exp (-V t x))) ≤
      (2 + 2 * C ^ 2) * (1 + ‖t‖ ^ 2) := by
  have hs := (sq_le_sq₀ (abs_nonneg (dx t 0))
    (by positivity : 0 ≤ C * (1 + ‖t‖))).mpr (hb t)
  rw [sq_abs, mul_pow] at hs
  have ht : (1 + ‖t‖) ^ 2 ≤ 2 * (1 + ‖t‖ ^ 2) := by
    nlinarith [sq_nonneg (‖t‖ - 1)]
  have hmul := mul_le_mul_of_nonneg_left ht (sq_nonneg C)
  have hsecond := strong_potential_raw_second_bound (V t) (dx t) (hcd t)
    (by norm_num : (0 : ℝ) < 1) (hd t) (hm t)
  simp only [div_one] at hsecond
  nlinarith [sq_nonneg ‖t‖]

/-- A global polynomial bound for the actual marginal Hessian follows
from primitive score growth and transverse strong convexity. -/
theorem vectorCoordinate_hessian_polynomial_growth {V : E → ℝ → ℝ}
    (H : RegularVectorCoordinateFamily V) (dx : E → ℝ → ℝ)
    (hcd : ∀ t, Continuous (dx t))
    (hd : ∀ t x, HasDerivAt (V t) (dx t x) x)
    (hm : ∀ t, Monotone (fun x => dx t x - 1 * x))
    {C S D : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hd0 : ∀ t, |dx t 0| ≤ C * (1 + ‖t‖))
    (hsb : ∀ t x, ‖H.score t x‖ ≤ S * (1 + ‖t‖ + |x|))
    (hHb : ∀ t x, ‖H.hessian t x‖ ≤ D * (1 + ‖t‖ ^ 2 + x ^ 2)) (t : E) :
    ‖vectorCoordinateHessian H t‖ ≤
      ((D + 6 * S ^ 2) * (3 + 2 * C ^ 2)) * (1 + ‖t‖ ^ 2) := by
  letI := vectorCoordinate_slice_probability H t
  have hx := (strong_potential_law_probability_and_memLp (V t) (dx t) (hcd t)
    (by norm_num : (0 : ℝ) < 1) (hd t) (hm t)).2
  have h := coordinate_hessian_polynomial_growth _ t (H.score t) (H.hessian t)
    (vectorCoordinate_score_memLp_two H t) (vectorCoordinate_hessian_integrable H t)
    hx hS hD (hsb t) (hHb t) (coordinate_slice_raw_second_growth V dx hcd hd hm hC hd0 t)
  change ‖vectorCoordinateHessian H t‖ ≤ _ at h
  convert h using 1 <;> first | rfl | ring

end
end Nonsmooth
