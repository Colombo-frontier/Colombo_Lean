import GradientHessian.GaussianConcentrationIntegrability
import Mathlib.Probability.Moments.MGFAnalytic

/-! Actual MGF and CGF derivatives for arbitrary Gaussian Lipschitz
functions. All exponential integrability premises are discharged. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert Set
open scoped NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_integrableExpSet_univ {f : E → ℝ} {B : ℝ≥0} (hLip : LipschitzWith B f) :
    integrableExpSet f (euclideanGaussianLaw E) = univ := by
  ext t
  simp only [integrableExpSet, mem_setOf_eq, mem_univ, iff_true]
  exact lipschitz_exponential_integrable hLip t

theorem gaussian_mgf_hasDerivAt {f : E → ℝ} {B : ℝ≥0} (hLip : LipschitzWith B f) (t : ℝ) :
    HasDerivAt (mgf f (euclideanGaussianLaw E))
      (∫ x, f x * Real.exp (t * f x) ∂euclideanGaussianLaw E) t := by
  apply hasDerivAt_mgf
  rw [gaussian_integrableExpSet_univ E hLip, interior_univ]
  trivial

theorem gaussian_cgf_hasDerivAt {f : E → ℝ} {B : ℝ≥0} (hLip : LipschitzWith B f) (t : ℝ) :
    HasDerivAt (cgf f (euclideanGaussianLaw E))
      ((∫ x, f x * Real.exp (t * f x) ∂euclideanGaussianLaw E) / mgf f (euclideanGaussianLaw E) t) t :=
  (gaussian_mgf_hasDerivAt E hLip t).log (mgf_pos (lipschitz_exponential_integrable hLip t)).ne'

theorem gaussian_cgf_hasDerivAt_zero {f : E → ℝ} {B : ℝ≥0} (hLip : LipschitzWith B f) :
    HasDerivAt (cgf f (euclideanGaussianLaw E)) (∫ x, f x ∂euclideanGaussianLaw E) 0 := by
  simpa only [zero_mul, Real.exp_zero, mul_one, mgf_zero, div_one] using
    gaussian_cgf_hasDerivAt E hLip 0

omit [BorelSpace E] in
theorem gaussian_centered_mgf_eq (f : E → ℝ) (t : ℝ) :
    (∫ x, Real.exp (t * (f x - ∫ y, f y ∂euclideanGaussianLaw E)) ∂euclideanGaussianLaw E) =
      mgf f (euclideanGaussianLaw E) t * Real.exp (-t * ∫ y, f y ∂euclideanGaussianLaw E) := by
  simpa only [sub_eq_add_neg, mul_neg, neg_mul, mgf] using
    (mgf_add_const (X := f) (μ := euclideanGaussianLaw E) (t := t)
      (-(∫ y, f y ∂euclideanGaussianLaw E)))

end GradientHessian.GaussianConcentration
