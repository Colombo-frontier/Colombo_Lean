import Nonsmooth.GaussianPairPotentialDensity
import Nonsmooth.GaussianPlaneCoordinates
import Nonsmooth.C2ProjectionImage

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPotentialLaw_plane_marginal (U : E → ℝ) (hU : Measurable U)
    (hd : Module.finrank ℝ E = 2)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ho : ⟪u, v⟫_ℝ = 0) :
    (gaussianPotentialLaw U).map (fun z : E => (⟪u, z⟫_ℝ, ⟪v, z⟫_ℝ)) =
      potentialJointLaw (fun t x => U (t • u + x • v)) := by
  let reconstruct : ℝ × ℝ → E := fun p => p.1 • u + p.2 • v
  let project : E → ℝ × ℝ := fun z => (⟪u, z⟫_ℝ, ⟪v, z⟫_ℝ)
  have hr : Measurable reconstruct := by fun_prop
  have hp : Measurable project := by fun_prop
  have hw : Measurable (gaussianPotentialWeight U) :=
    (((continuous_norm.pow 2).measurable.div_const 2).sub hU).exp
  have hrec : ((gaussianReal 0 1).prod (gaussianReal 0 1)).map reconstruct =
      euclideanGaussianLaw E := euclideanGaussian_plane_reconstruction hd hu hv ho
  have hid : project ∘ reconstruct = id := by
    funext p
    exact orthonormal_pair_reconstruction_coordinates hu hv ho p.1 p.2
  have hweight : (fun p : ℝ × ℝ => gaussianPotentialWeight U (reconstruct p)) =
      fun p : ℝ × ℝ => Real.exp ((p.1 ^ 2 + p.2 ^ 2) / 2 - U (p.1 • u + p.2 • v)) := by
    funext p
    rw [gaussianPotentialWeight]
    dsimp only [reconstruct]
    rw [orthonormal_pair_reconstruction_norm hu hv ho]
  change (weightedDensityLaw (euclideanGaussianLaw E) (gaussianPotentialWeight U)).map project = _
  rw [← hrec, ← weightedDensityLaw_map _ reconstruct hr _ hw,
    Measure.map_map hp hr, hid, Measure.map_id, hweight]
  exact standardGaussian_pair_potential_law (fun t x => U (t • u + x • v)) (hU.comp hr)

theorem c2_gaussian_plane_regular_image {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ)
    (hd : Module.finrank ℝ E = 2)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ho : ⟪u, v⟫_ℝ = 0) :
    Nonempty (RegularProjectionImage (gaussianPotentialLaw U) u v) := by
  have hov : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact ho
  apply regularProjectionImage_exists_of_c2_plane (gaussianPotentialLaw U) u v hU hρ v u hv hu hov
  have h := gaussianPotentialLaw_plane_marginal U hU.smooth.continuous.measurable hd hu hv ho
  simpa only [planePoint, real_inner_comm u] using h

end
end Nonsmooth
