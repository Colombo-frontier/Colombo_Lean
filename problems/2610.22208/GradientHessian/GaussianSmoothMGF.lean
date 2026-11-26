import GradientHessian.GaussianTiltEntropy
import GradientHessian.GaussianHerbstCalculus

/-! Sharp centered Gaussian MGF bound for actual bounded C2 functions.
The entropy differential inequality is derived from log-Sobolev. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert
open scoped NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_smooth_cgf_bound_pos {f : E → ℝ} {B C : ℝ≥0} {D : ℝ}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (hD : ∀ x, ‖f x‖ ≤ D) {t : ℝ} (ht : 0 < t) :
    cgf f (euclideanGaussianLaw E) t ≤
      t * (∫ x, f x ∂euclideanGaussianLaw E) + t ^ 2 * (B : ℝ) ^ 2 / 2 := by
  have hd (s : ℝ) : HasDerivAt (cgf f (euclideanGaussianLaw E))
      (deriv (cgf f (euclideanGaussianLaw E)) s) s :=
    (gaussian_cgf_hasDerivAt E hLip s).differentiableAt.hasDerivAt
  have h := herbst_calculus (c := (B : ℝ) ^ 2 / 2) hd cgf_zero
    (fun s _ => by
      convert gaussian_cgf_differential_bound E hf hLip hH hD s using 1
      ring) ht
  rw [(gaussian_cgf_hasDerivAt_zero E hLip).deriv] at h
  nlinarith only [h]

theorem gaussian_smooth_centered_mgf_pos {f : E → ℝ} {B C : ℝ≥0} {D : ℝ}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (hD : ∀ x, ‖f x‖ ≤ D) {t : ℝ} (ht : 0 < t) :
    (∫ x, Real.exp (t * (f x - ∫ y, f y ∂euclideanGaussianLaw E)) ∂euclideanGaussianLaw E) ≤
      Real.exp (t ^ 2 * (B : ℝ) ^ 2 / 2) := by
  have h := gaussian_smooth_cgf_bound_pos E hf hLip hH hD ht
  have hp := mgf_pos (lipschitz_exponential_integrable hLip t)
  have he : mgf f (euclideanGaussianLaw E) t = Real.exp (cgf f (euclideanGaussianLaw E) t) :=
    (Real.exp_log hp).symm
  rw [gaussian_centered_mgf_eq, he, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [h]

theorem gaussian_smooth_centered_mgf {f : E → ℝ} {B C : ℝ≥0} {D : ℝ}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (hD : ∀ x, ‖f x‖ ≤ D) (t : ℝ) :
    (∫ x, Real.exp (t * (f x - ∫ y, f y ∂euclideanGaussianLaw E)) ∂euclideanGaussianLaw E) ≤
      Real.exp (t ^ 2 * (B : ℝ) ^ 2 / 2) := by
  rcases lt_trichotomy 0 t with ht | ht | ht
  · exact gaussian_smooth_centered_mgf_pos E hf hLip hH hD ht
  · subst t
    simp
  · have hneg (x : E) : ‖fderiv ℝ (fderiv ℝ (fun y => -f y)) x‖ ≤ (C : ℝ) := by
      have he : fderiv ℝ (fun y => -f y) = fun y => -fderiv ℝ f y := funext (fun _ => fderiv_neg)
      rw [he, fderiv_neg, ContinuousLinearMap.opNorm_neg]
      exact hH x
    have h := gaussian_smooth_centered_mgf_pos E hf.neg hLip.neg hneg
      (fun x => by simpa only [norm_neg] using hD x) (neg_pos.mpr ht)
    have he (x : E) : -t * (-f x - ∫ y, -f y ∂euclideanGaussianLaw E) =
        t * (f x - ∫ y, f y ∂euclideanGaussianLaw E) := by rw [integral_neg]; ring
    simpa only [he, neg_sq] using h

end GradientHessian.GaussianConcentration
