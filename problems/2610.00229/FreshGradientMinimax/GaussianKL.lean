import FreshGradientMinimax.GaussianMoments
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! The actual KL divergence between equal-variance Gaussian probability
measures, derived from their Radon–Nikodym derivatives. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal

theorem gaussianReal_mutual_ac (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal m v ≪ gaussianReal n v :=
  (gaussianReal_absolutelyContinuous m hv).trans (gaussianReal_absolutelyContinuous' n hv)

theorem gaussianPDFReal_log_difference (m n x : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Real.log (gaussianPDFReal m v x) - Real.log (gaussianPDFReal n v x) =
      ((m - n) / (v : ℝ)) * x + (n ^ 2 - m ^ 2) / (2 * (v : ℝ)) := by
  have hv0 : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hc : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 := by positivity
  simp only [gaussianPDFReal, Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp]
  field_simp
  ring

theorem gaussianReal_llr (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    llr (gaussianReal m v) (gaussianReal n v) =ᵐ[gaussianReal m v]
      (fun x : ℝ => ((m - n) / (v : ℝ)) * x + (n ^ 2 - m ^ 2) / (2 * (v : ℝ))) := by
  have hr := Measure.rnDeriv_withDensity_right (gaussianReal m v) volume
    (measurable_gaussianPDF n v).aemeasurable
    (Filter.Eventually.of_forall (fun x => (gaussianPDF_pos n hv x).ne'))
    (Filter.Eventually.of_forall (fun _ => gaussianPDF_ne_top))
  rw [← gaussianReal_of_var_ne_zero n hv] at hr
  apply (gaussianReal_absolutelyContinuous m hv).ae_eq
  filter_upwards [hr, rnDeriv_gaussianReal m v] with x hx hy
  rw [llr, hx, hy, ENNReal.toReal_mul, ENNReal.toReal_inv,
    toReal_gaussianPDF, toReal_gaussianPDF,
    Real.log_mul (inv_ne_zero (gaussianPDFReal_pos n v x hv).ne') (gaussianPDFReal_pos m v x hv).ne',
    Real.log_inv]
  have h := gaussianPDFReal_log_difference m n x hv
  linarith

theorem gaussianReal_llr_integrable (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (llr (gaussianReal m v) (gaussianReal n v)) (gaussianReal m v) := by
  apply (integrable_congr (gaussianReal_llr m n hv)).mpr
  exact ((gaussianReal_id_integrable m v).const_mul _).add (integrable_const _)

theorem gaussianReal_klDiv (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal m v) (gaussianReal n v) =
      ENNReal.ofReal ((m - n) ^ 2 / (2 * (v : ℝ))) := by
  rw [klDiv_of_ac_of_integrable (gaussianReal_mutual_ac m n hv) (gaussianReal_llr_integrable m n hv),
    integral_congr_ae (gaussianReal_llr m n hv),
    integral_add (f := fun x : ℝ => ((m - n) / (v : ℝ)) * x)
      (g := fun _ : ℝ => (n ^ 2 - m ^ 2) / (2 * (v : ℝ)))
      ((gaussianReal_id_integrable m v).const_mul _) (integrable_const _),
    integral_const_mul, gaussianReal_mean]
  simp only [integral_const, measureReal_univ_eq_one, one_smul, add_sub_cancel_right]
  congr 1
  ring

end FreshGradientMinimax
