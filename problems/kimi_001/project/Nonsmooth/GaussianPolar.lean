import Nonsmooth.GaussianDirection
import Nonsmooth.RadialIndependence

open MeasureTheory ProbabilityTheory Metric Filter Function
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussianLaw_polar :
    Measure.map (fun z : E => (‖z‖, normalizedDirection z)) (euclideanGaussianLaw E) =
      (Measure.map (fun z : E => ‖z‖) (euclideanGaussianLaw E)).prod (sphericalLaw E) :=
  rotational_radius_direction_product _ euclideanGaussianLaw_nonzero euclideanGaussianLaw_isometry

theorem truncatedGaussianLaw_polar :
    Measure.map (fun z : E => (‖z‖, normalizedDirection z)) (truncatedGaussianLaw E) =
      (Measure.map (fun z : E => ‖z‖) (truncatedGaussianLaw E)).prod (sphericalLaw E) :=
  rotational_radius_direction_product _ truncatedGaussianLaw_nonzero truncatedGaussianLaw_isometry

theorem truncatedGaussianLaw_radial_reconstruct :
    Measure.map (fun p : ℝ × E => p.1 • p.2)
      ((Measure.map (fun z : E => ‖z‖) (truncatedGaussianLaw E)).prod (sphericalLaw E)) =
        truncatedGaussianLaw E := by
  rw [← truncatedGaussianLaw_polar, Measure.map_map (g := fun p : ℝ × E => p.1 • p.2) (measurable_fst.smul measurable_snd)
    (continuous_norm.measurable.prodMk normalizedDirection_measurable)]
  have hid : ((fun p : ℝ × E => p.1 • p.2) ∘
      (fun z : E => (‖z‖, normalizedDirection z))) = id :=
    funext normalizedDirection_reconstruct
  rw [hid]
  exact Measure.map_id

end
end Nonsmooth
