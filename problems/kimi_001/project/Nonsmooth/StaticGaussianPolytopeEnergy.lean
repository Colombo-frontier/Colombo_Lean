import Nonsmooth.C2GaussianRegularImages
import Nonsmooth.GaussianPolytopeCovariance
import Nonsmooth.GaussianPolytopeScaling

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]

theorem strict_soft_gaussian_polytope_regular_images (c : E) (R : ℝ)
    (a : ι → E) (b : ι → ℝ) (n : ℕ)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ho : ⟪u, v⟫_ℝ = 0) :
    Nonempty (RegularProjectionImage
      (weightedDensityLaw (euclideanGaussianLaw E)
        (strictSoftInequalityWeight (ballPolytopeConstraint c R a b) n)) u v) := by
  have hρ : 1 < 1 + 2 / ((n : ℝ) + 1) := by
    have hp : 0 < 2 / ((n : ℝ) + 1) := by positivity
    linarith
  have h := c2StrongQuadraticPotential_regular_images
    (strictGaussianBallPolytopePotential_c2Strong c R a b n) hρ hu hv ho
  simpa only [gaussianPotentialLaw, strictSoftInequalityWeight_gaussian_potential] using h

/-- The actual static Gaussian ball-polytope row family satisfies the
logarithmic one-step energy bound, with all analytic images constructed. -/
theorem gaussian_ball_polytope_actual_log_energy {n : ℕ}
    (c : Fin (n + 1) → E) (R : Fin (n + 1) → ℝ) (hR : ∀ i, 0 ≤ R i)
    (a : Fin (n + 1) → ι → E) (b : Fin (n + 1) → ι → ℝ)
    (hpos : ∀ i, euclideanGaussianLaw E (closedBall (c i) (R i) ∩
      {z : E | ∀ j, ⟪a i j, z⟫_ℝ ≤ b i j}) ≠ 0)
    {u : E} (hu : ‖u‖ = 1) (hd : 2 ≤ Module.finrank ℝ E) :
    let A := fun i => closedBall (c i) (R i) ∩ {z : E | ∀ j, ⟪a i j, z⟫_ℝ ≤ b i j}
    letI (i : Fin (n + 1)) : IsProbabilityMeasure (euclideanGaussianLaw E)[|A i] :=
      cond_isProbabilityMeasure (hpos i)
    (∫ h, ‖posteriorAggregateShift (Measure.pi (fun i => (euclideanGaussianLaw E)[|A i]))
      (supportSingleObservation u) h‖ ^ 2
      ∂(Measure.pi (fun i => (euclideanGaussianLaw E)[|A i])).map (supportSingleObservation u)) ≤
        512 * Real.log (Real.exp 1 * ((n + 1 : ℕ) : ℝ)) :=
  gaussian_ball_polytope_log_energy_of_regular_images c R hR a b hpos hu hd
    (fun i m v hv ho => Classical.choice
      (strict_soft_gaussian_polytope_regular_images (c i) (R i) (a i) (b i) m hu hv ho))

theorem gaussian_ball_polytope_actual_scaled_log_energy {n : ℕ}
    (c : Fin (n + 1) → E) (R : Fin (n + 1) → ℝ) (hR : ∀ i, 0 ≤ R i)
    (a : Fin (n + 1) → ι → E) (b : Fin (n + 1) → ι → ℝ)
    (hpos : ∀ i, euclideanGaussianLaw E (closedBall (c i) (R i) ∩
      {z : E | ∀ j, ⟪a i j, z⟫_ℝ ≤ b i j}) ≠ 0)
    {u : E} (hu : ‖u‖ = 1) (hd : 2 ≤ Module.finrank ℝ E) :
    let A := fun i => closedBall (c i) (R i) ∩ {z : E | ∀ j, ⟪a i j, z⟫_ℝ ≤ b i j}
    letI (i : Fin (n + 1)) : IsProbabilityMeasure (euclideanGaussianLaw E)[|A i] :=
      cond_isProbabilityMeasure (hpos i)
    let Q := Measure.pi (fun i => (euclideanGaussianLaw E)[|A i])
    let s := (Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹
    letI : IsProbabilityMeasure (Q.map (scaleSupportRows s)) :=
      Measure.isProbabilityMeasure_map (scaleSupportRows_measurable s).aemeasurable
    (∫ h, ‖posteriorAggregateShift (Q.map (scaleSupportRows s)) (supportSingleObservation u) h‖ ^ 2
      ∂(Q.map (scaleSupportRows s)).map (supportSingleObservation u)) ≤
      512 * Real.log (Real.exp 1 * ((n + 1 : ℕ) : ℝ)) / (Module.finrank ℝ E : ℝ) :=
  gaussian_ball_polytope_scaled_log_energy c R hR a b hpos hu hd
    (fun i m v hv ho => Classical.choice
      (strict_soft_gaussian_polytope_regular_images (c i) (R i) (a i) (b i) m hu hv ho))

end
end Nonsmooth
