import Nonsmooth.AffineObservationPosterior
import Nonsmooth.SoftWeightCDF

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

theorem affine_observation_cdf (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (r : α → ℝ) (hr : Measurable r)
    (X : β → ℝ) (hX : Measurable X) {c : ℝ} (hc : 0 < c) (a : ℝ)
    (hobs : ∀ z, X (f z) = a + c * r z) (y : ℝ) :
    cdf ((μ.map f).map X) y = cdf (μ.map r) ((y - a) / c) := by
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure ((μ.map f).map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  letI : IsProbabilityMeasure (μ.map r) := Measure.isProbabilityMeasure_map hr.aemeasurable
  rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply hX measurableSet_Iic,
    map_measureReal_apply hf (hX measurableSet_Iic), map_measureReal_apply hr measurableSet_Iic]
  congr 1
  ext z
  simp only [mem_preimage, mem_Iic, hobs]
  rw [le_div_iff₀ hc]
  constructor <;> intro h <;> nlinarith

end
end Nonsmooth
