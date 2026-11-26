import Nonsmooth.SpanningProjectionRank
import Nonsmooth.GaussianPolytopeProjectionRank
import Nonsmooth.GaussianPolytopeConcentration
import Nonsmooth.SpanningGaussianPotentialLaw

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]

theorem gaussian_ball_polytope_projection_rank_all_dimensions (c : E) {R : ℝ} (hR : 0 ≤ R)
    (a : ι → E) (b : ι → ℝ)
    (hp : euclideanGaussianLaw E (closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}) ≠ 0)
    {u : E} (hu : ‖u‖ = 1) :
    let μ := (euclideanGaussianLaw E)[|closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}]
    letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure hp
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      ‖projectionPosteriorShift μ u y‖ ^ 2 ≤
        72 * (1 + rankQuantileLog (cdf (μ.map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
  by_cases hd : 2 ≤ Module.finrank ℝ E
  · exact gaussian_ball_polytope_projection_rank c hR a b hp hu hd
  have hd1 : Module.finrank ℝ E = 1 := by have hp := Module.finrank_pos (R := ℝ) (M := E); omega
  let μ := (euclideanGaussianLaw E)[|closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}]
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure hp
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hr := spanning_unit_projection_rank μ hu (unit_spans_of_finrank_one hu hd1)
    (gaussian_polytope_projection_atomless c R a b hu0)
    (fun t => by simpa only [real_inner_comm u] using
      (gaussian_ball_polytope_centered_mgf c hR a b hp u t).1)
    (fun t => by simpa only [real_inner_comm u, hu, one_pow, mul_one] using
      (gaussian_ball_polytope_centered_mgf c hR a b hp u t).2)
  filter_upwards [hr] with y hy
  nlinarith [sq_nonneg ‖projectionPosteriorShift μ u y‖]

end
end Nonsmooth
