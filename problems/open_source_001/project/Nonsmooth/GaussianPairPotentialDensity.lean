import Nonsmooth.GaussianPotentialDensity
import Nonsmooth.PotentialJointDensity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem standardGaussian_pair_pdf_cancel (V : ℝ → ℝ → ℝ) (t x : ℝ) :
    gaussianPDFReal 0 1 t * gaussianPDFReal 0 1 x *
      Real.exp ((t ^ 2 + x ^ 2) / 2 - V t x) =
        ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 * Real.exp (-V t x) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have he : -(t ^ 2) / 2 + -(x ^ 2) / 2 + ((t ^ 2 + x ^ 2) / 2 - V t x) = -V t x := by ring
  calc
    _ = ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 *
        (Real.exp (-(t ^ 2) / 2) * Real.exp (-(x ^ 2) / 2) *
          Real.exp ((t ^ 2 + x ^ 2) / 2 - V t x)) := by ring
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, he]

theorem standardGaussian_pair_potential_raw_density (V : ℝ → ℝ → ℝ)
    (hV : Measurable (Function.uncurry V)) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).withDensity
      (fun p => ENNReal.ofReal (Real.exp ((p.1 ^ 2 + p.2 ^ 2) / 2 - V p.1 p.2))) =
        ENNReal.ofReal (((Real.sqrt (2 * Real.pi))⁻¹) ^ 2) • potentialJointMeasure V := by
  let w : ℝ × ℝ → ℝ := fun p => Real.exp ((p.1 ^ 2 + p.2 ^ 2) / 2 - V p.1 p.2)
  have hw : Measurable w :=
    ((((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).div_const 2).sub hV).exp
  have hpdf : Measurable (fun p : ℝ × ℝ => gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2) :=
    ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd)
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0),
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    ← withDensity_mul _ hpdf hw.ennreal_ofReal]
  have he : (fun p : ℝ × ℝ => gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2) *
      (fun p => ENNReal.ofReal (w p)) =
        ENNReal.ofReal (((Real.sqrt (2 * Real.pi))⁻¹) ^ 2) •
          (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-V p.1 p.2))) := by
    funext p
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, gaussianPDF_def]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 p.1),
      ← ENNReal.ofReal_mul (mul_nonneg (gaussianPDFReal_nonneg 0 1 p.1) (gaussianPDFReal_nonneg 0 1 p.2))]
    dsimp only [w]
    rw [standardGaussian_pair_pdf_cancel, ENNReal.ofReal_mul (sq_nonneg _)]
  change ((volume : Measure ℝ).prod volume).withDensity
    ((fun p : ℝ × ℝ => gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2) *
      (fun p => ENNReal.ofReal (w p))) = _
  have hwm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-V p.1 p.2))) :=
    hV.neg.exp.ennreal_ofReal
  rw [he, withDensity_smul _ hwm]
  rfl

theorem standardGaussian_pair_potential_law (V : ℝ → ℝ → ℝ)
    (hV : Measurable (Function.uncurry V)) :
    weightedDensityLaw ((gaussianReal 0 1).prod (gaussianReal 0 1))
      (fun p => Real.exp ((p.1 ^ 2 + p.2 ^ 2) / 2 - V p.1 p.2)) = potentialJointLaw V := by
  rw [weightedDensityLaw, standardGaussian_pair_potential_raw_density V hV,
    normalized_measure_smul _ _ (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top]
  rfl

end
end Nonsmooth
