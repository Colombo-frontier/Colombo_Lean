import Nonsmooth.GaussianPolytopeScalar
import Nonsmooth.AffineObservationPosterior

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι β : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
local instance (K : Submodule ℝ E) : BorelSpace K := Subtype.borelSpace _

theorem gaussian_polytope_affine_scalar_posterior {u : E} (hu : ‖u‖ = 1)
    [Nontrivial (ℝ ∙ u)ᗮ] {R : ℝ} (hR : 0 ≤ R) (a : ι → E) (b : ι → ℝ)
    (hp : euclideanGaussianLaw E (closedBall (0 : E) R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}) ≠ 0)
    (f : E → β) (hf : Measurable f) (X : β → ℝ) (hX : Measurable X)
    {c : ℝ} (hc : c ≠ 0) (o : ℝ) (hXf : ∀ z, X (f z) = o + c * ⟪z, u⟫_ℝ) :
    let A := closedBall (0 : E) R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}
    ∀ᵐ y ∂(((euclideanGaussianLaw E)[|A]).map f).map X,
      let t := (y - o) / c
      let B := closedBall (0 : (ℝ ∙ u)ᗮ) (Real.sqrt (R ^ 2 - t ^ 2)) ∩
        {z : (ℝ ∙ u)ᗮ | ∀ j, ⟪(ℝ ∙ u)ᗮ.orthogonalProjection (a j), z⟫_ℝ ≤ b j - t * ⟪a j, u⟫_ℝ}
      0 < R ^ 2 - t ^ 2 ∧ euclideanGaussianLaw (ℝ ∙ u)ᗮ B ≠ 0 ∧
      condDistrib id X (((euclideanGaussianLaw E)[|A]).map f) y =
        ((euclideanGaussianLaw (ℝ ∙ u)ᗮ)[|B]).map (fun z : (ℝ ∙ u)ᗮ => f (t • u + (z : E))) := by
  let A := closedBall (0 : E) R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}
  let μ := (euclideanGaussianLaw E)[|A]
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure hp
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) := by fun_prop
  let B (t : ℝ) := closedBall (0 : (ℝ ∙ u)ᗮ) (Real.sqrt (R ^ 2 - t ^ 2)) ∩
    {z : (ℝ ∙ u)ᗮ | ∀ j, ⟪(ℝ ∙ u)ᗮ.orthogonalProjection (a j), z⟫_ℝ ≤ b j - t * ⟪a j, u⟫_ℝ}
  let P (t : ℝ) (ν : Measure β) :=
    0 < R ^ 2 - t ^ 2 ∧ euclideanGaussianLaw (ℝ ∙ u)ᗮ (B t) ≠ 0 ∧
      ν = ((euclideanGaussianLaw (ℝ ∙ u)ᗮ)[|B t]).map
        (fun z : (ℝ ∙ u)ᗮ => f (t • u + (z : E)))
  change ∀ᵐ y ∂(μ.map f).map X, P ((y - o) / c) (condDistrib id X (μ.map f) y)
  apply affine_observation_posterior_property μ f hf _ hr X hX hc o hXf P
  filter_upwards [gaussian_polytope_scalar_subspace_posterior hu hR a b] with t ht
  refine ⟨ht.1, ht.2.1, ?_⟩
  change (condDistrib id (fun z : E => ⟪z, u⟫_ℝ) ((euclideanGaussianLaw E)[|A]) t).map f = _
  rw [ht.2.2, Measure.map_map hf (by fun_prop)]
  rfl

end
end Nonsmooth
