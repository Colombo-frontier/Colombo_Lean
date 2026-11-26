import GaussianEntropy254
import Mathlib.InformationTheory.KullbackLeibler.Basic

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal
namespace Paper254

theorem gaussian_llr_density (u m : ℝ) (q c : ℝ≥0) (hq : q ≠ 0) (hc : c ≠ 0) :
    llr (gaussianReal u q) (gaussianReal m c) =ᵐ[gaussianReal u q]
      fun x => Real.log (gaussianPDFReal u q x/gaussianPDFReal m c x) := by
  have hr := Measure.rnDeriv_withDensity_right (gaussianReal u q) volume
    (measurable_gaussianPDF m c).aemeasurable
    (ae_of_all _ (fun x => (gaussianPDF_pos m hc x).ne'))
    (ae_of_all _ (fun _ => gaussianPDF_ne_top))
  rw [← gaussianReal_of_var_ne_zero m hc] at hr
  have hqvol := gaussianReal_absolutelyContinuous u hq
  filter_upwards [hqvol.ae_le hr,hqvol.ae_le (rnDeriv_gaussianReal u q)] with x hx hy
  rw [llr,hx,hy,ENNReal.toReal_mul,ENNReal.toReal_inv,toReal_gaussianPDF,toReal_gaussianPDF]
  congr 1
  ring

theorem gaussian_llr_integrable (u m : ℝ) (q c : ℝ≥0) (hq : q ≠ 0) (hc : c ≠ 0) :
    Integrable (llr (gaussianReal u q) (gaussianReal m c)) (gaussianReal u q) := by
  have h := (integrable_const (Real.log ((c:ℝ)/(q:ℝ))/2)).add
    ((((gaussian_centered_integrable u m q).div_const (c:ℝ)).sub
      ((gaussian_centered_integrable u u q).div_const (q:ℝ))).div_const 2)
  have he := gaussian_llr_density u m q c hq hc
  apply h.congr
  filter_upwards [he] with x hx
  rw [hx,gaussian_log_density_ratio u m x q c hq hc]
  rfl

/-- Finite KL between two genuine Gaussian probability measures. -/
theorem gaussian_kl_formula (u m : ℝ) (q c : ℝ≥0) (hq : q ≠ 0) (hc : c ≠ 0) :
    klDiv (gaussianReal u q) (gaussianReal m c)=ENNReal.ofReal (coordinateKL q c (u-m)) := by
  have hac := (gaussianReal_absolutelyContinuous u hq).trans (gaussianReal_absolutelyContinuous' m hc)
  rw [klDiv_of_ac_of_integrable hac (gaussian_llr_integrable u m q c hq hc)]
  rw [integral_congr_ae (gaussian_llr_density u m q c hq hc),gaussian_density_entropy u m q c hq hc]
  simp

end Paper254
#print axioms Paper254.gaussian_kl_formula
