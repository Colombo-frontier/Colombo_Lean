import Nonsmooth.GaussianPolytopeModel
import Nonsmooth.GaussianPolytopeAffinePosterior

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
local instance (M : GaussianPolytopeModel E) (K : Submodule ℝ M.Space) : BorelSpace K :=
  Subtype.borelSpace _

def gaussianPolytopeWinnerModel (s : ℝ) (M : GaussianPolytopeModel E)
    (u : M.Space) [Nontrivial (ℝ ∙ u)ᗮ] (t : ℝ)
    (hp : euclideanGaussianLaw (ℝ ∙ u)ᗮ
      (gaussianBallPolytope (Real.sqrt (M.radius ^ 2 - t ^ 2))
        (fun j => (ℝ ∙ u)ᗮ.orthogonalProjection (M.normal j))
        (fun j => M.bound j - t * ⟪M.normal j, u⟫_ℝ)) ≠ 0) : GaussianPolytopeModel E where
  Space := (ℝ ∙ u)ᗮ
  Index := M.Index
  embedding := M.embedding.comp (ℝ ∙ u)ᗮ.subtypeₗᵢ
  origin := M.origin + s • M.embedding (t • u)
  radius := Real.sqrt (M.radius ^ 2 - t ^ 2)
  radius_nonneg := Real.sqrt_nonneg _
  normal := fun j => (ℝ ∙ u)ᗮ.orthogonalProjection (M.normal j)
  bound := fun j => M.bound j - t * ⟪M.normal j, u⟫_ℝ
  positive := hp

theorem gaussianPolytopeWinnerModel_map (s : ℝ) (M : GaussianPolytopeModel E)
    (u : M.Space) [Nontrivial (ℝ ∙ u)ᗮ] (t : ℝ)
    (hp : euclideanGaussianLaw (ℝ ∙ u)ᗮ
      (gaussianBallPolytope (Real.sqrt (M.radius ^ 2 - t ^ 2))
        (fun j => (ℝ ∙ u)ᗮ.orthogonalProjection (M.normal j))
        (fun j => M.bound j - t * ⟪M.normal j, u⟫_ℝ)) ≠ 0)
    (z : (ℝ ∙ u)ᗮ) :
    gaussianPolytopeModelMap s (gaussianPolytopeWinnerModel s M u t hp) z =
      gaussianPolytopeModelMap s M (t • u + (z : M.Space)) := by
  simp [gaussianPolytopeModelMap, gaussianPolytopeWinnerModel, map_add, smul_add, add_assoc] <;> rfl

/-- A winner slice with a nontrivial residual space has an explicit new model
at the same scale, including its positive Gaussian conditioning mass. -/
theorem gaussianPolytopeModel_normalized_projection_closed (s : ℝ) (M : GaussianPolytopeModel E)
    {u : M.Space} (hu : ‖u‖ = 1) [Nontrivial (ℝ ∙ u)ᗮ]
    (X : E → ℝ) (hX : Measurable X) {c : ℝ} (hc : c ≠ 0) (o : ℝ)
    (hXf : ∀ z, X (gaussianPolytopeModelMap s M z) = o + c * ⟪z, u⟫_ℝ) :
    ∀ᵐ y ∂(gaussianPolytopeModelLaw s M).map X,
      GaussianPolytopeRow s (condDistrib id X (gaussianPolytopeModelLaw s M) y) := by
  have h := gaussian_polytope_affine_scalar_posterior hu M.radius_nonneg M.normal M.bound
    M.positive (gaussianPolytopeModelMap s M) (gaussianPolytopeModelMap_measurable s M)
    X hX hc o hXf
  filter_upwards [h] with y hy
  let t := (y - o) / c
  let M' := gaussianPolytopeWinnerModel s M u t hy.2.1
  refine Or.inr ⟨M', ?_⟩
  refine hy.2.2.trans ?_
  change _ = ((euclideanGaussianLaw (ℝ ∙ u)ᗮ)[|_]).map (gaussianPolytopeModelMap s M')
  congr 1
  funext z
  exact (gaussianPolytopeWinnerModel_map s M u t hy.2.1 z).symm

end
end Nonsmooth
