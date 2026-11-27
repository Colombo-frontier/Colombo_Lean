import Nonsmooth.WeightedProductMarginal
import Nonsmooth.WeightedJointDisintegration

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

theorem normalized_measure_smul (μ : Measure α) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hct : c ≠ ∞) : (c • μ)[|univ] = μ[|univ] := by
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply,
    smul_eq_mul, smul_smul]
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  have he : c⁻¹ * (μ univ)⁻¹ * c = (μ univ)⁻¹ := by
    calc
      _ = (c⁻¹ * c) * (μ univ)⁻¹ := by ac_rfl
      _ = (μ univ)⁻¹ := by rw [ENNReal.inv_mul_cancel hc0 hct, one_mul]
  rw [he]

theorem weightedDensityLaw_const_mul (μ : Measure α) (w : α → ℝ)
    (hw : Measurable w) (c : ℝ) (hc : 0 < c) :
    weightedDensityLaw μ (fun x => c * w x) = weightedDensityLaw μ w := by
  have he : (fun x => ENNReal.ofReal (c * w x)) =
      ENNReal.ofReal c • (fun x => ENNReal.ofReal (w x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul hc.le]
  rw [weightedDensityLaw, he, withDensity_smul _ hw.ennreal_ofReal,
    normalized_measure_smul _ _ (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top]
  rfl

theorem weightedDensityLaw_map (μ : Measure α) (f : α → β) (hf : Measurable f)
    (w : β → ℝ) (hw : Measurable w) :
    (weightedDensityLaw μ (fun x => w (f x))).map f =
      weightedDensityLaw (μ.map f) w := by
  have hraw := map_withDensity_comp μ f hf (fun y => ENNReal.ofReal (w y)) hw.ennreal_ofReal
  have hcond := conditioning_map_preimage
    (μ.withDensity (fun x => ENNReal.ofReal (w (f x)))) f hf univ MeasurableSet.univ
  simpa only [Set.preimage_univ, weightedDensityLaw, hraw] using hcond.symm

end
end Nonsmooth
