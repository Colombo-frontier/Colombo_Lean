import Nonsmooth.GaussianEventSlices
import Nonsmooth.GaussianPolytopeWeights

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]

def gaussianRadialPolytopeSlice (R : ℝ) (a : ι → E) (b : ι → ℝ) (x : E) : Set E :=
  {z : E | ‖z‖ ^ 2 ≤ R ^ 2 - ‖x‖ ^ 2 ∧ ∀ j, ⟪a j, z⟫_ℝ ≤ b j - ⟪a j, x⟫_ℝ}

theorem gaussianRadialPolytopeSlice_measurable (R : ℝ) (a : ι → E) (b : ι → ℝ) (x : E) :
    MeasurableSet (gaussianRadialPolytopeSlice R a b x) := by
  have hm (j : ι) : Measurable (fun z : E => ⟪a j, z⟫_ℝ) := by fun_prop
  have hcut : MeasurableSet {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j - ⟪a j, x⟫_ℝ} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_le (hm j) measurable_const)
  exact (measurableSet_le (continuous_norm.pow 2).measurable measurable_const).inter hcut

theorem gaussian_polytope_slice_event (K : Submodule ℝ E) {R : ℝ} (hR : 0 ≤ R)
    (a : ι → E) (b : ι → ℝ) {x : E} (hx : x ∈ K) :
    ((fun z : E => x + z) ⁻¹' (closedBall (0 : E) R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}))
      =ᵐ[gaussianOrthogonalResidualLaw K] gaussianRadialPolytopeSlice R a b x := by
  filter_upwards [gaussian_slice_ball_radial K hx hR] with z hz
  apply propext
  have hball : x + z ∈ closedBall (0 : E) R ↔ ‖z‖ ^ 2 ≤ R ^ 2 - ‖x‖ ^ 2 :=
    Iff.of_eq hz
  change (x + z ∈ closedBall (0 : E) R ∧ ∀ j, ⟪a j, x + z⟫_ℝ ≤ b j) ↔
    (‖z‖ ^ 2 ≤ R ^ 2 - ‖x‖ ^ 2 ∧ ∀ j, ⟪a j, z⟫_ℝ ≤ b j - ⟪a j, x⟫_ℝ)
  simp only [hball, inner_add_right, le_sub_iff_add_le, add_comm]

/-- Any fixed linear projection of a Gaussian ball-polytope law has an actual
affine Gaussian residual posterior with the translated halfspace cuts. -/
theorem gaussian_polytope_projection_posterior (K : Submodule ℝ E) {R : ℝ} (hR : 0 ≤ R)
    (a : ι → E) (b : ι → ℝ) :
    let A := closedBall (0 : E) R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}
    ∀ᵐ x ∂((euclideanGaussianLaw E)[|A]).map (fun z : E => (K.orthogonalProjection z : E)),
      condDistrib id (fun z : E => (K.orthogonalProjection z : E)) ((euclideanGaussianLaw E)[|A]) x =
        ((gaussianOrthogonalResidualLaw K)[|gaussianRadialPolytopeSlice R a b x]).map (fun z => x + z) ∧
      gaussianOrthogonalResidualLaw K (gaussianRadialPolytopeSlice R a b x) ≠ 0 := by
  let A := closedBall (0 : E) R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j}
  have hA : MeasurableSet A := by
    change MeasurableSet (closedBall (0 : E) R ∩ {z : E | ∀ j, ⟪a j, z⟫_ℝ ≤ b j})
    rw [← ballPolytopeConstraint_region (0 : E) hR a b]
    exact softInequalityRegion_measurable _
      (fun j => (ballPolytopeConstraint_contDiff (0 : E) R a b j).continuous.measurable)
  have he := gaussian_event_projection_posterior K A hA
  have hmem : ∀ᵐ x ∂((euclideanGaussianLaw E)[|A]).map (fun z : E => (K.orthogonalProjection z : E)), x ∈ K :=
    (ae_map_iff (K.subtypeL.comp K.orthogonalProjection).measurable.aemeasurable
      K.closed_of_finiteDimensional.measurableSet).mpr
      (Eventually.of_forall (fun z => (K.orthogonalProjection z).property))
  filter_upwards [he, hmem] with x hx hK
  have hset := gaussian_polytope_slice_event K hR a b hK
  change ((fun z : E => x + z) ⁻¹' A) =ᵐ[gaussianOrthogonalResidualLaw K]
    gaussianRadialPolytopeSlice R a b x at hset
  have hcond : (gaussianOrthogonalResidualLaw K)[|(fun z => x + z) ⁻¹' A] =
      (gaussianOrthogonalResidualLaw K)[|gaussianRadialPolytopeSlice R a b x] := by
    simp only [ProbabilityTheory.cond, measure_congr hset, Measure.restrict_congr_set hset]
  rw [hcond, measure_congr hset] at hx
  exact hx

end
end Nonsmooth
