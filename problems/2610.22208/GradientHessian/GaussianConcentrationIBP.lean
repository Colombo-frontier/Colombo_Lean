import GradientHessian.GaussianConcentrationIntegrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Gaussian integration by parts with explicit integrability hypotheses.
The identity is proved from the actual Gaussian density, not postulated. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem standard_density_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have he : gaussianPDFReal 0 1 = fun y =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    funext y
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [he]
  convert (((((hasDerivAt_id x).pow 2).neg).div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹) using 1
  simp only [id_eq]
  ring

theorem standard_gaussian_integrable_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]

/-- The one-coordinate Gaussian integration-by-parts identity, with precise
growth conditions expressed as the three necessary integrabilities. -/
theorem standard_gaussian_integration_by_parts {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hfD := standard_gaussian_integrable_iff.mp hf
  have hf'D := standard_gaussian_integrable_iff.mp hf'
  have hxfD := standard_gaussian_integrable_iff.mp hxf
  have hleft : Integrable (f * fun x => -x * gaussianPDFReal 0 1 x) := by
    convert hxfD.neg using 1
    funext x
    simp only [Pi.mul_apply, Pi.neg_apply]
    ring
  have hright : Integrable (f' * gaussianPDFReal 0 1) := by
    simpa only [Pi.mul_apply, mul_comm] using hf'D
  have htotal : Integrable (f * gaussianPDFReal 0 1) := by
    simpa only [Pi.mul_apply, mul_comm] using hfD
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable hd
    standard_density_hasDerivAt hleft hright htotal
  have hlefteq : (∫ x, f x * (-x * gaussianPDFReal 0 1 x)) =
      -(∫ x, gaussianPDFReal 0 1 x * (x * f x)) := by
    rw [← integral_neg]
    congr 1
    funext x
    ring
  rw [hlefteq] at hi
  have hrightEq : (∫ x, f' x * gaussianPDFReal 0 1 x) =
      ∫ x, gaussianPDFReal 0 1 x * f' x := by
    congr 1
    funext x
    ring
  rw [hrightEq] at hi
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  exact neg_injective hi

end GradientHessian.GaussianConcentration
