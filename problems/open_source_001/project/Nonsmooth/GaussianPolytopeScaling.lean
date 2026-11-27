import Nonsmooth.SupportEnergyScaling
import Nonsmooth.GaussianPolytopeEnergy

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem support_aggregate_energy_dimension_scale {k : ℕ} [Nonempty (Fin k)]
    (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q] (u : E) {B : ℝ}
    (hB : (∫ h, ‖posteriorAggregateShift Q (supportSingleObservation u) h‖ ^ 2
      ∂Q.map (supportSingleObservation u)) ≤ B) :
    let c := (Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹
    letI : IsProbabilityMeasure (Q.map (scaleSupportRows c)) :=
      Measure.isProbabilityMeasure_map (scaleSupportRows_measurable c).aemeasurable
    (∫ h, ‖posteriorAggregateShift (Q.map (scaleSupportRows c)) (supportSingleObservation u) h‖ ^ 2
      ∂(Q.map (scaleSupportRows c)).map (supportSingleObservation u)) ≤ B / (Module.finrank ℝ E : ℝ) := by
  let c := (Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹
  letI : IsProbabilityMeasure (Q.map (scaleSupportRows c)) :=
    Measure.isProbabilityMeasure_map (scaleSupportRows_measurable c).aemeasurable
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hd)
  have h := mul_le_mul_of_nonneg_left hB (sq_nonneg c)
  change (∫ h, ‖posteriorAggregateShift (Q.map (scaleSupportRows c)) (supportSingleObservation u) h‖ ^ 2
    ∂(Q.map (scaleSupportRows c)).map (supportSingleObservation u)) ≤ B / (Module.finrank ℝ E : ℝ)
  rw [support_aggregate_energy_scale Q u hc]
  simpa only [c, inv_pow, Real.sq_sqrt hd.le, div_eq_inv_mul] using h

/-- The actual Gaussian ball-polytope criterion at the manuscript's dimension
scale. Only the explicitly specified regular soft-image construction remains
an analytic hypothesis; all scaling and posterior identities are proved. -/
theorem gaussian_ball_polytope_scaled_log_energy [Fintype ι] {n : ℕ}
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
    let Q := Measure.pi (fun i => (euclideanGaussianLaw E)[|A i])
    let s := (Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹
    letI : IsProbabilityMeasure (Q.map (scaleSupportRows s)) :=
      Measure.isProbabilityMeasure_map (scaleSupportRows_measurable s).aemeasurable
    (∫ h, ‖posteriorAggregateShift (Q.map (scaleSupportRows s)) (supportSingleObservation u) h‖ ^ 2
      ∂(Q.map (scaleSupportRows s)).map (supportSingleObservation u)) ≤
      512 * Real.log (Real.exp 1 * ((n + 1 : ℕ) : ℝ)) / (Module.finrank ℝ E : ℝ) := by
  let A := fun i => closedBall (c i) (R i) ∩ {z : E | ∀ j, ⟪a i j, z⟫_ℝ ≤ b i j}
  letI (i : Fin (n + 1)) : IsProbabilityMeasure (euclideanGaussianLaw E)[|A i] :=
    cond_isProbabilityMeasure (hpos i)
  exact support_aggregate_energy_dimension_scale
    (Measure.pi (fun i => (euclideanGaussianLaw E)[|A i])) u
    (gaussian_ball_polytope_log_energy_of_regular_images c R hR a b hpos hu hd H)

end
end Nonsmooth
