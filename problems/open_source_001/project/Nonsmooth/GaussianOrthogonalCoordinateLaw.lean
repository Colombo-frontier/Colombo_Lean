import Nonsmooth.GaussianAxisDecomposition
import Nonsmooth.GaussianSubspaceLaw
import Nonsmooth.OrthogonalCoordinateBounds

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
local instance (K : Submodule ℝ E) : BorelSpace K := Subtype.borelSpace _

theorem orthogonal_complement_axis_inner (u : E) (t : (ℝ ∙ u)ᗮ) :
    ⟪(t : E), u⟫_ℝ = 0 := by
  exact (Submodule.mem_orthogonal_singleton_iff_inner_left.mp t.property)

theorem orthogonal_complement_coordinate_projection (u : E) (t : (ℝ ∙ u)ᗮ) (x : ℝ) :
    (ℝ ∙ u)ᗮ.orthogonalProjectionOnto ((t : E) + x • u) = t := by
  rw [map_add, map_smul, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, smul_zero, add_zero]

/-- A standard Gaussian is reconstructed from the independent standard
Gaussian on an axis complement and the standard scalar Gaussian. -/
theorem euclideanGaussian_complement_axis_reconstruction {u : E} (hu : ‖u‖ = 1)
    [Nontrivial (ℝ ∙ u)ᗮ] :
    ((euclideanGaussianLaw (ℝ ∙ u)ᗮ).prod (gaussianReal 0 1)).map
      (fun p : (ℝ ∙ u)ᗮ × ℝ => (p.1 : E) + p.2 • u) = euclideanGaussianLaw E := by
  have h := euclideanGaussian_axis_reconstruction hu
  rw [gaussianOrthogonalResidualLaw_subspace] at h
  have hsub : Measurable ((ℝ ∙ u)ᗮ.subtype : (ℝ ∙ u)ᗮ → E) :=
    (ℝ ∙ u)ᗮ.subtypeL.measurable
  have hp := Measure.map_prod_map (euclideanGaussianLaw (ℝ ∙ u)ᗮ)
    (gaussianReal 0 1) hsub measurable_id
  simp only [Measure.map_id] at hp
  rw [hp, Measure.map_map (by fun_prop) (hsub.prodMap measurable_id)] at h
  change ((euclideanGaussianLaw (ℝ ∙ u)ᗮ).prod (gaussianReal 0 1)).map
    (fun p : (ℝ ∙ u)ᗮ × ℝ => p.2 • u + (p.1 : E)) = euclideanGaussianLaw E at h
  simpa only [add_comm] using h

end
end Nonsmooth
