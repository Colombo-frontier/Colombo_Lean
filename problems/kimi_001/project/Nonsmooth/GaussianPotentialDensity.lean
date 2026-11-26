import Nonsmooth.WeightedLawTransport
import Nonsmooth.GaussianIntervalMGF
import Nonsmooth.GaussianPrior

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def gaussianPotentialWeight {E : Type} [NormedAddCommGroup E] (U : E → ℝ) (z : E) : ℝ :=
  Real.exp (‖z‖ ^ 2 / 2 - U z)

def gaussianPotentialLaw {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (U : E → ℝ) : Measure E :=
  weightedDensityLaw (euclideanGaussianLaw E) (gaussianPotentialWeight U)

theorem standardGaussian_pdf_cancel (U : ℝ → ℝ) (A x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (A + x ^ 2 / 2 - U x) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp A * Real.exp (-U x) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  have he : -(x ^ 2) / 2 + (A + x ^ 2 / 2 - U x) = A + -U x := by ring
  rw [he, Real.exp_add, ← mul_assoc]

theorem standardGaussian_potential_raw_density (U : ℝ → ℝ) (hU : Measurable U) :
    (gaussianReal 0 1).withDensity (fun x => ENNReal.ofReal (gaussianPotentialWeight U x)) =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) •
        volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x))) := by
  have hw : Measurable (gaussianPotentialWeight U) :=
    (((continuous_norm.pow 2).measurable.div_const 2).sub hU).exp
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0),
    ← withDensity_mul _ (measurable_gaussianPDF 0 1) hw.ennreal_ofReal]
  have he : gaussianPDF 0 1 * (fun x => ENNReal.ofReal (gaussianPotentialWeight U x)) =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) •
        (fun x => ENNReal.ofReal (Real.exp (-U x))) := by
    funext x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, gaussianPDF_def]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
    have hx := standardGaussian_pdf_cancel U 0 x
    simp only [zero_add, Real.exp_zero, mul_one] at hx
    simpa only [gaussianPotentialWeight, Real.norm_eq_abs, sq_abs, hx,
      ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹)]
  rw [he]
  exact withDensity_smul _ (show Measurable (fun x => ENNReal.ofReal (Real.exp (-U x))) by fun_prop)

theorem standardGaussian_potential_law (U : ℝ → ℝ) (hU : Measurable U) :
    weightedDensityLaw (gaussianReal 0 1) (gaussianPotentialWeight U) =
      realDensityLaw (fun x => Real.exp (-U x)) := by
  rw [weightedDensityLaw, standardGaussian_potential_raw_density U hU,
    normalized_measure_smul _ _ (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      ENNReal.ofReal_ne_top]
  rfl

end
end Nonsmooth
