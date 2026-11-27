import Nonsmooth.GaussianPolytopeWeights
import Nonsmooth.SoftGaussianDamping
import Nonsmooth.SoftConditionedSupportEnergy
import Nonsmooth.GaussianLinearMGF

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]

/-- For actual independent Gaussian rows conditioned to a ball and finitely many
halfspaces, all base moments, approximation weights, boundary nullity and limiting
identities are proved. The only analytic image hypothesis is regularity of the
specified strictly convex soft two-coordinate laws. -/
theorem gaussian_ball_polytope_log_energy_of_regular_images {n : ℕ}
    (c : Fin (n + 1) → E) (R : Fin (n + 1) → ℝ) (hR : ∀ i, 0 ≤ R i)
    (a : Fin (n + 1) → ι → E) (b : Fin (n + 1) → ι → ℝ)
    (hpos : ∀ i, euclideanGaussianLaw E (closedBall (c i) (R i) ∩
      {z : E | ∀ j, ⟪a i j, z⟫_ℝ ≤ b i j}) ≠ 0)
    {u : E} (hu : ‖u‖ = 1) (hd : 2 ≤ Module.finrank ℝ E)
    (H : ∀ i m (v : E), ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 →
      RegularProjectionImage (weightedDensityLaw (euclideanGaussianLaw E)
        (strictSoftInequalityWeight (ballPolytopeConstraint (c i) (R i) (a i) (b i)) m)) u v) :
    let A := fun i => closedBall (c i) (R i) ∩ {z : E | ∀ j, ⟪a i j, z⟫_ℝ ≤ b i j}
    letI (i : Fin (n + 1)) : IsProbabilityMeasure (euclideanGaussianLaw E)[|A i] :=
      cond_isProbabilityMeasure (hpos i)
    (∫ h, ‖posteriorAggregateShift (Measure.pi (fun i => (euclideanGaussianLaw E)[|A i]))
      (supportSingleObservation u) h‖ ^ 2
      ∂(Measure.pi (fun i => (euclideanGaussianLaw E)[|A i])).map (supportSingleObservation u)) ≤
        512 * Real.log (Real.exp 1 * ((n + 1 : ℕ) : ℝ)) := by
  let f := fun i => ballPolytopeConstraint (c i) (R i) (a i) (b i)
  let A := fun i => closedBall (c i) (R i) ∩ {z : E | ∀ j, ⟪a i j, z⟫_ℝ ≤ b i j}
  have hreg (i : Fin (n + 1)) : softInequalityRegion (f i) = A i :=
    ballPolytopeConstraint_region (c i) (hR i) (a i) (b i)
  have hf (i : Fin (n + 1)) (j : Option ι) : ContDiff ℝ ⊤ (f i j) :=
    ballPolytopeConstraint_contDiff (c i) (R i) (a i) (b i) j
  have hA (i : Fin (n + 1)) : MeasurableSet (A i) := by
    rw [← hreg i]
    exact softInequalityRegion_measurable (f i) (fun j => (hf i j).continuous.measurable)
  have hlim (i : Fin (n + 1)) : ∀ᵐ z ∂euclideanGaussianLaw E,
      Tendsto (fun m => strictSoftInequalityWeight (f i) m z) atTop
        (𝓝 ((A i).indicator (fun _ => (1 : ℝ)) z)) := by
    rw [← hreg i]
    exact strictSoftInequalityWeight_ae_tendsto (euclideanGaussianLaw E) (f i)
      (ballPolytopeConstraint_gaussian_boundary_zero (c i) (R i) (a i) (b i))
  have hu0 : u ≠ 0 := by intro h; simp only [h, norm_zero] at hu; norm_num at hu
  exact soft_conditioned_support_log_energy (fun _ : Fin (n + 1) => euclideanGaussianLaw E)
    (fun _ => (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      euclideanGaussian_norm_square_integrable)
    (fun _ => euclideanGaussian_exp_inner_integrable) hu hd
    (fun _ y => by simpa only [real_inner_comm _ u] using euclideanGaussian_hyperplane_zero hu0 y)
    (fun i => strictSoftInequalityWeight (f i))
    (fun i m => (strictSoftInequalityWeight_contDiff (f i) (hf i) m).continuous.measurable)
    (fun i m z => ⟨(strictSoftInequalityWeight_bounds (f i) m z).1.le,
      (strictSoftInequalityWeight_bounds (f i) m z).2⟩)
    (fun i m => Eventually.of_forall (fun z => (strictSoftInequalityWeight_bounds (f i) m z).1))
    A hA hpos hlim H

end
end Nonsmooth
