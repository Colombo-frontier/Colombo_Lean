import Nonsmooth.GaussianPrior

open MeasureTheory ProbabilityTheory Metric Filter Function
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem truncatedGaussianLaw_apply (s : Set E) :
    truncatedGaussianLaw E s =
      (euclideanGaussianLaw E (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))))⁻¹ *
        euclideanGaussianLaw E (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E)) ∩ s) :=
  cond_apply measurableSet_closedBall (euclideanGaussianLaw E) s

theorem gaussianSupportRowLaw_integral {f : E → ℝ} (hf : Continuous f) :
    (∫ a : Feasible E 2, f a.val ∂gaussianSupportRowLaw E) =
      ∫ z : E, f ((Real.sqrt (Module.finrank ℝ E))⁻¹ • z) ∂truncatedGaussianLaw E := by
  have hc : StronglyMeasurable (fun a : Feasible E 2 => f a.val) :=
    (hf.comp continuous_subtype_val).stronglyMeasurable
  rw [gaussianSupportRowLaw, integral_map_of_stronglyMeasurable gaussianScaleRow_measurable hc]
  change (∫ z : Feasible E (2 * Real.sqrt (Module.finrank ℝ E)),
    f ((Real.sqrt (Module.finrank ℝ E))⁻¹ • z.val) ∂truncatedGaussianVectorLaw E) = _
  exact truncatedGaussianVectorLaw_integral (E := E)
    (fun z : E => f ((Real.sqrt (Module.finrank ℝ E))⁻¹ • z))

theorem gaussianScaleRow_measurePreserving :
    MeasurePreserving (gaussianScaleRow (E := E)) (truncatedGaussianVectorLaw E) (gaussianSupportRowLaw E) :=
  ⟨gaussianScaleRow_measurable, rfl⟩

theorem gaussianSupportPrior_rescaled (k : ℕ) :
    Measure.map (rescaledSupportRows (E := E) (ι := Fin k) Module.finrank_pos)
      (Measure.pi (fun _ : Fin k => truncatedGaussianVectorLaw E)) = gaussianSupportPrior E k := by
  have hp := measurePreserving_pi (fun _ : Fin k => truncatedGaussianVectorLaw E)
    (fun _ : Fin k => gaussianSupportRowLaw E) (fun _ => gaussianScaleRow_measurePreserving (E := E))
  exact hp.map_eq

end
end Nonsmooth
