import Nonsmooth.GaussianTruncated
import Nonsmooth.GaussianCharacteristic

open MeasureTheory ProbabilityTheory Metric Function
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def gaussianAmbientRowLaw (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] : Measure E :=
  Measure.map (Subtype.val : Feasible E 2 → E) (gaussianSupportRowLaw E)

instance gaussianAmbientRowLaw_probability : IsProbabilityMeasure (gaussianAmbientRowLaw E) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem truncatedGaussianLaw_isometry (e : E ≃ₗᵢ[ℝ] E) :
    Measure.map e (truncatedGaussianLaw E) = truncatedGaussianLaw E := by
  let B := closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))
  have hpre : e ⁻¹' B = B := by
    ext z
    simp only [B, Set.mem_preimage, mem_closedBall, dist_zero_right, e.norm_map]
  have he := Measure.restrict_map (μ := euclideanGaussianLaw E) e.continuous.measurable
    (show MeasurableSet B from measurableSet_closedBall)
  rw [hpre, euclideanGaussianLaw_isometry] at he
  unfold truncatedGaussianLaw ProbabilityTheory.cond
  rw [Measure.map_smul]
  change _ • Measure.map e ((euclideanGaussianLaw E).restrict B) = _
  rw [← he]

theorem gaussianAmbientRowLaw_isometry (e : E ≃ₗᵢ[ℝ] E) :
    Measure.map e (gaussianAmbientRowLaw E) = gaussianAmbientRowLaw E := by
  have hm : Measurable (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) :=
    measurable_const.smul measurable_id
  rw [gaussianAmbientRowLaw, gaussianSupportRowLaw_map, Measure.map_map e.continuous.measurable hm]
  have he : e ∘ (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) =
      (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) ∘ e := funext (fun z => e.map_smul _ z)
  rw [he, ← Measure.map_map hm e.continuous.measurable, truncatedGaussianLaw_isometry]

end
end Nonsmooth
