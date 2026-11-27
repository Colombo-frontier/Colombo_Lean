import Nonsmooth.GaussianPolytopeSelectionClosure
import Nonsmooth.ParametricSelection

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E α : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace α] {n : ℕ}

theorem gaussianPolytope_independent_observation_rows {s : ℝ} (hs : 0 < s)
    (Q : Measure (Fin (n + 1) → E)) [IsProbabilityMeasure Q]
    (hi : iIndepFun (fun i (a : Fin (n + 1) → E) => a i) Q)
    (hrow : ∀ i, GaussianPolytopeRow s (Q.map (fun a => a i))) (q : E) :
    ∀ᵐ y ∂Q.map (supportSingleObservation q),
      ∀ i, GaussianPolytopeRow s
        ((condDistrib id (supportSingleObservation q) Q y).map (fun a => a i)) := by
  let μ (i : Fin (n + 1)) := Q.map (fun a => a i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  have hprod : Q = Measure.pi μ := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin (n + 1) => (measurable_pi_apply i).aemeasurable)).mp hi
    change Q.map id = Measure.pi μ at h
    simpa only [Measure.map_id] using h
  have h := gaussianPolytopeSingleObservation_rows_closed hs μ hrow q
  simp only [← hprod] at h
  exact h

/-- At each fixed history with independent represented rows, the actual
parameter-dependent posterior update has represented rows almost surely. -/
theorem gaussianPolytope_posterior_update_at {s : ℝ} (hs : 0 < s)
    (κ : Kernel α (Fin (n + 1) → E)) [IsMarkovKernel κ] (u : α → E) (hu : Measurable u)
    (x : α) (hi : iIndepFun (fun i (a : Fin (n + 1) → E) => a i) (κ x))
    (hrow : ∀ i, GaussianPolytopeRow s ((κ x).map (fun a => a i))) :
    ∀ᵐ y ∂(κ x).map (supportSingleObservation (u x)),
      ∀ i, GaussianPolytopeRow s
        ((supportPosteriorUpdate κ u hu (x, y)).map (fun a => a i)) := by
  have hp := observedPosterior_ae_eq_condDistrib κ
    (fun p : α × (Fin (n + 1) → E) => supportSingleObservation (u p.1) p.2)
    (supportParametricObservation_measurable u hu) x
  change ∀ᵐ y ∂(κ x).map (supportSingleObservation (u x)),
    supportPosteriorUpdate κ u hu (x, y) =
      condDistrib id (supportSingleObservation (u x)) (κ x) y at hp
  filter_upwards [hp, gaussianPolytope_independent_observation_rows hs (κ x) hi hrow (u x)]
    with y he hy
  rw [he]
  exact hy

theorem gaussianPolytope_two_conditional_observations {s : ℝ} (hs : 0 < s)
    (ν : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, GaussianPolytopeRow s (ν i)) (q : E) (u : Fin (n + 1) × ℝ → E) :
    let Q := Measure.pi ν
    let κ := condDistrib id (supportSingleObservation q) Q
    ∀ᵐ h ∂Q.map (supportSingleObservation q),
      ∀ᵐ y ∂(κ h).map (supportSingleObservation (u h)),
        ∀ i, GaussianPolytopeRow s
          ((condDistrib id (supportSingleObservation (u h)) (κ h) y).map (fun a => a i)) := by
  filter_upwards [gaussianPolytopeSingleObservation_rows_closed hs ν hν q,
    supportSingleObservation_posterior_independent ν q] with h hh hi
  exact gaussianPolytope_independent_observation_rows hs _ hi hh (u h)

end
end Nonsmooth
