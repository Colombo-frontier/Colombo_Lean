import Nonsmooth.StaticGaussianPolytopeEnergy
import Nonsmooth.SoftProjectionRank

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]

theorem gaussian_polytope_projection_atomless (c : E) (R : ℝ) (a : ι → E) (b : ι → ℝ)
    {u : E} (hu : u ≠ 0) (y : ℝ) :
    (euclideanGaussianLaw E)[|closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}]
      {z : E | ⟪z, u⟫_ℝ = y} = 0 := by
  apply cond_absolutelyContinuous
  simpa only [real_inner_comm u] using euclideanGaussian_hyperplane_zero hu y

theorem gaussian_ball_polytope_projection_rank (c : E) {R : ℝ} (hR : 0 ≤ R)
    (a : ι → E) (b : ι → ℝ)
    (hp : euclideanGaussianLaw E (closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}) ≠ 0)
    {u : E} (hu : ‖u‖ = 1) (hd : 2 ≤ Module.finrank ℝ E) :
    let μ := (euclideanGaussianLaw E)[|closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}]
    letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure hp
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      ‖projectionPosteriorShift μ u y‖ ^ 2 ≤
        72 * (1 + rankQuantileLog (cdf (μ.map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
  let f := ballPolytopeConstraint c R a b
  let A := closedBall c R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}
  have hregion : softInequalityRegion f = A := ballPolytopeConstraint_region c hR a b
  have hf (j : Option ι) : ContDiff ℝ ⊤ (f j) := ballPolytopeConstraint_contDiff c R a b j
  have hA : MeasurableSet A := by
    rw [← hregion]
    exact softInequalityRegion_measurable f (fun j => (hf j).continuous.measurable)
  have hlim : ∀ᵐ z ∂euclideanGaussianLaw E,
      Tendsto (fun n => strictSoftInequalityWeight f n z) atTop
        (𝓝 (A.indicator (fun _ => (1 : ℝ)) z)) := by
    rw [← hregion]
    exact strictSoftInequalityWeight_ae_tendsto (euclideanGaussianLaw E) f
      (ballPolytopeConstraint_gaussian_boundary_zero c R a b)
  have hL : MemLp (fun z : E => z) 2 (euclideanGaussianLaw E) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      euclideanGaussian_norm_square_integrable
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  apply soft_projection_rank_bound (euclideanGaussianLaw E) (hL.integrable (by norm_num)) hu hd
    (fun y => by simpa only [real_inner_comm u] using euclideanGaussian_hyperplane_zero hu0 y)
    (strictSoftInequalityWeight f)
    (fun n => (strictSoftInequalityWeight_contDiff f hf n).continuous.measurable)
    (fun n z => ⟨(strictSoftInequalityWeight_bounds f n z).1.le,
      (strictSoftInequalityWeight_bounds f n z).2⟩)
    (fun n => Eventually.of_forall (fun z => (strictSoftInequalityWeight_bounds f n z).1))
    A hA hp hlim
  intro n v hv ho
  exact Classical.choice (strict_soft_gaussian_polytope_regular_images c R a b n hu hv ho)

end
end Nonsmooth
