import Nonsmooth.GaussianPolytopeSubspace

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]

local instance (K : Submodule ℝ E) : BorelSpace K := Subtype.borelSpace _

/-- The actual projection posterior remains a Gaussian ball-polytope law on
the remaining subspace, translated by the observed projection. The positive
radius and positive Gaussian mass are conclusions of disintegration. -/
theorem gaussian_polytope_projection_subspace_posterior
    (K : Submodule ℝ E) [Nontrivial Kᗮ] {R : ℝ} (hR : 0 ≤ R)
    (a : ι → E) (b : ι → ℝ) :
    let A := closedBall (0 : E) R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}
    ∀ᵐ x ∂((euclideanGaussianLaw E)[|A]).map (fun z : E => (K.orthogonalProjection z : E)),
      let B := closedBall (0 : Kᗮ) (Real.sqrt (R ^ 2 - ‖x‖ ^ 2)) ∩
        {z : Kᗮ | ∀ j, ⟪Kᗮ.orthogonalProjection (a j), z⟫_ℝ ≤ b j - ⟪a j, x⟫_ℝ}
      0 < R ^ 2 - ‖x‖ ^ 2 ∧ euclideanGaussianLaw Kᗮ B ≠ 0 ∧
      condDistrib id (fun z : E => (K.orthogonalProjection z : E)) ((euclideanGaussianLaw E)[|A]) x =
        ((euclideanGaussianLaw Kᗮ)[|B]).map (fun z : Kᗮ => x + (z : E)) := by
  filter_upwards [gaussian_polytope_projection_posterior K hR a b] with x hx
  have hδ := gaussian_radial_polytope_positive_radius K R a b x hx.2
  have hB := gaussian_radial_polytope_subspace_event K R a b x hδ.le
  have hsub : Measurable Kᗮ.subtype := Kᗮ.subtypeL.measurable
  have hp := hx.2
  rw [gaussianOrthogonalResidualLaw_subspace K,
    Measure.map_apply hsub (gaussianRadialPolytopeSlice_measurable R a b x), hB] at hp
  refine ⟨hδ, hp, ?_⟩
  rw [hx.1, gaussian_radial_polytope_subspace K R a b x, hB]

end
end Nonsmooth
