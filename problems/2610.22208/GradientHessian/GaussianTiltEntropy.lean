import GradientHessian.GaussianExponentialJets
import GradientHessian.GaussianMGFCalculus

/-! The entropy differential inequality for the actual Gaussian CGF.
The exponential-tilt premises of log-Sobolev are proved, not assumed. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert
open scoped NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem gaussian_tilt_entropy {f : E → ℝ} {B C : ℝ≥0} {D : ℝ}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (hD : ∀ x, ‖f x‖ ≤ D) (t : ℝ) :
    t * (∫ x, f x * Real.exp (t * f x) ∂euclideanGaussianLaw E) -
        mgf f (euclideanGaussianLaw E) t * Real.log (mgf f (euclideanGaussianLaw E) t) ≤
      (t ^ 2 * (B : ℝ) ^ 2 / 2) * mgf f (euclideanGaussianLaw E) t := by
  obtain ⟨B', C', hL, hJ⟩ := exponentialTilt_bounded_jets hf hLip hH hD t
  have hc := exponentialTilt_contDiff hf t
  have hval := exponentialTilt_value_bounds hD t
  have hls := gaussian_logSobolev_bounded_smooth E hc hL hJ
    (Real.exp_pos (-|t| * D)) hval
  have hi := fisher_integrable E hc hL (Real.exp_pos (-|t| * D)) (fun x => (hval x).1)
  have hg : Integrable (exponentialTilt f t) (euclideanGaussianLaw E) :=
    lipschitz_exponential_integrable hLip t
  have hb := integral_mono hi (hg.const_mul (t ^ 2 * (B : ℝ) ^ 2))
    (fun x => exponentialTilt_fisher_bound (hf.differentiable (by norm_num)) hLip t x)
  rw [integral_const_mul] at hb
  have hleft : (∫ x, exponentialTilt f t x * Real.log (exponentialTilt f t x)
      ∂euclideanGaussianLaw E) = t * ∫ x, f x * Real.exp (t * f x) ∂euclideanGaussianLaw E := by
    simp only [exponentialTilt, Real.log_exp]
    have he (x : E) : Real.exp (t * f x) * (t * f x) = t * (f x * Real.exp (t * f x)) := by ring
    simp_rw [he]
    exact integral_const_mul _ _
  rw [hleft] at hls
  have hfin := hls.trans (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1 / 2))
  change t * (∫ x, f x * Real.exp (t * f x) ∂euclideanGaussianLaw E) -
    mgf f (euclideanGaussianLaw E) t * Real.log (mgf f (euclideanGaussianLaw E) t) ≤
      (1 / 2 : ℝ) * ((t ^ 2 * (B : ℝ) ^ 2) * mgf f (euclideanGaussianLaw E) t) at hfin
  nlinarith only [hfin]

theorem gaussian_cgf_differential_bound {f : E → ℝ} {B C : ℝ≥0} {D : ℝ}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (hD : ∀ x, ‖f x‖ ≤ D) (t : ℝ) :
    t * deriv (cgf f (euclideanGaussianLaw E)) t - cgf f (euclideanGaussianLaw E) t ≤
      t ^ 2 * (B : ℝ) ^ 2 / 2 := by
  have hp := mgf_pos (lipschitz_exponential_integrable hLip t)
  rw [(gaussian_cgf_hasDerivAt E hLip t).deriv, cgf]
  have he : t * ((∫ x, f x * Real.exp (t * f x) ∂euclideanGaussianLaw E) /
      mgf f (euclideanGaussianLaw E) t) - Real.log (mgf f (euclideanGaussianLaw E) t) =
      (t * (∫ x, f x * Real.exp (t * f x) ∂euclideanGaussianLaw E) -
        mgf f (euclideanGaussianLaw E) t * Real.log (mgf f (euclideanGaussianLaw E) t)) /
        mgf f (euclideanGaussianLaw E) t := by field_simp
  rw [he]
  exact (div_le_iff₀ hp).mpr (gaussian_tilt_entropy E hf hLip hH hD t)

end GradientHessian.GaussianConcentration
