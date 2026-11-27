import Nonsmooth.SoftplusDerivatives
import Nonsmooth.QuadraticSoftPotentialBounds
import Nonsmooth.VectorCoordinateGrowth

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem softplus_composition_hasFDerivAt (U : E → ℝ) (s : E →L[ℝ] ℝ) (x : E)
    (hU : HasFDerivAt U s x) :
    HasFDerivAt (fun z => softplus (U z)) (softplusSlope (U x) • s) x :=
  (softplus_hasDerivAt (U x)).comp_hasFDerivAt x hU

theorem softplus_vector_score_hasFDerivAt (U : E → ℝ) (s : E → E →L[ℝ] ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (hU : HasFDerivAt U (s x) x) (hs : HasFDerivAt s H x) :
    HasFDerivAt (fun z => softplusSlope (U z) • s z)
      (softplusSlope (U x) • H + softplusCurvature (U x) • (s x).smulRight (s x)) x := by
  have hc := (softplusSlope_hasDerivAt (U x)).comp_hasFDerivAt x hU
  convert! hc.smul hs using 1
  ext v w
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Function.comp_apply]
  ring

theorem softplus_hessian_symmetric (z : ℝ) (s : E →L[ℝ] ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ v w, H v w = H w v) (v w : E) :
    (softplusSlope z • H + softplusCurvature z • s.smulRight s) v w =
      (softplusSlope z • H + softplusCurvature z • s.smulRight s) w v := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hsym v w]
  ring

theorem softplus_hessian_nonnegative (z : ℝ) (s : E →L[ℝ] ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : ∀ v, 0 ≤ H v v) (v : E) :
    0 ≤ (softplusSlope z • H + softplusCurvature z • s.smulRight s) v v := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  have h1 := mul_nonneg (softplusSlope_bounds z).1.le (hH v)
  have h2 := mul_nonneg (softplusCurvature_bounds z).1.le (sq_nonneg (s v))
  nlinarith

theorem softplus_hessian_norm_bound (z : ℝ) (s : E →L[ℝ] ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖softplusSlope z • H + softplusCurvature z • s.smulRight s‖ ≤ ‖H‖ + ‖s‖ ^ 2 := by
  have hn := norm_add_le (softplusSlope z • H) (softplusCurvature z • s.smulRight s)
  have hn1 := ContinuousLinearMap.opNorm_smul_le (softplusSlope z) H
  have hn2 := ContinuousLinearMap.opNorm_smul_le (softplusCurvature z) (s.smulRight s)
  rw [Real.norm_eq_abs, abs_of_pos (softplusSlope_bounds z).1] at hn1
  rw [Real.norm_eq_abs, abs_of_pos (softplusCurvature_bounds z).1,
    ContinuousLinearMap.norm_smulRight_apply, ← pow_two] at hn2
  have h1 := mul_le_mul_of_nonneg_right (softplusSlope_bounds z).2.le (norm_nonneg H)
  have h2 := mul_le_mul_of_nonneg_right (show softplusCurvature z ≤ 1 by
    linarith [(softplusCurvature_bounds z).2]) (sq_nonneg ‖s‖)
  nlinarith

theorem softplus_quadratic_envelope (U : E → ℝ) {B : ℝ}
    (hb : ∀ z, |U z| ≤ B * (1 + ‖z‖ ^ 2)) (z : E) :
    softplus (U z) ≤ (Real.log 2 + B) * (1 + ‖z‖ ^ 2) := by
  have h := softplus_upper_abs (U z)
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [hb z, mul_nonneg hl (sq_nonneg ‖z‖)]

end
end Nonsmooth
