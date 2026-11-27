import AdaptiveSphereStoppedSpan
import AdaptiveSphereStoppedEnergy
import AdaptiveSphereMeasurementProjection

/-! The manuscript's general sphere-fiber energy lemma for the ORIGINAL
protocol and an arbitrary measurable low-rank event. -/
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Task006.AdaptiveSphereOriginalEnergy
open Task006.Full Task006.Full.OracleAlgorithm Task006.HaarRebalancing
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereState Task006.AdaptiveSphereTranscript
open Task006.AdaptiveSphereAction Task006.AdaptiveSphereStopped Task006.AdaptiveSphereMean
open Task006.AdaptiveSphereStoppedEnergy Task006.AdaptiveSphereEnergyDrift
open Task006.AdaptiveSphereSpan Task006.AdaptiveSphereStoppedSpan Task006.StoppedEnergy
noncomputable section
variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

/-- Event energy for any original measurable adaptive linear protocol. Even
ambient-measurable events are allowed; transcript-measurable ones are included. -/
theorem original_event_center_energy_le (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (event : Set (OrthogonalGroup d)) (hevent : MeasurableSet event)
    (hbelow : ∀ Q ∈ event,
      Module.finrank ℝ (measurementSpanBefore A weight tape seed N (column Q j)) < k) :
    (∫ Q in event, ‖actualCenter A weight tape seed d le_rfl N j Q‖^2
      ∂orthogonalHaarProbability d) ≤ rankPotential d k := by
  have hOriginal : Integrable (fun Q => ‖actualCenter A weight tape seed d le_rfl N j Q‖^2)
      (orthogonalHaarProbability d) :=
    centerEnergy_integrable A weight tape seed d le_rfl N le_rfl j
  have hStopped : Integrable (fun Q =>
      ‖actualCenter (stoppedObserver A weight tape seed k hkd) weight tape () k hkd N j Q‖^2)
      (orthogonalHaarProbability d) :=
    centerEnergy_integrable _ _ _ _ _ _ N le_rfl j
  have htransfer := event_energy_le_stopped_energy event hevent
    (fun Q => ‖actualCenter A weight tape seed d le_rfl N j Q‖^2)
    (fun Q => ‖actualCenter (stoppedObserver A weight tape seed k hkd) weight tape () k hkd N j Q‖^2)
    hOriginal hStopped (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun Q hQ => congrArg (fun x : E d => ‖x‖^2)
      (below_dimension_center_eq A weight tape seed k hkd j Q (hbelow Q hQ))))
  exact htransfer.trans (stoppedObserver_expected_center_energy_le A weight tape seed k hkd j)

/-- Full L2, in the actual measurement-span/projection notation of the paper.
No posterior moment or stopped-energy hypothesis occurs among its premises. -/
theorem original_sphere_fiber_energy (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (event : Set (OrthogonalGroup d)) (hevent : MeasurableSet event)
    (hbelow : ∀ Q ∈ event,
      Module.finrank ℝ (measurementSpanBefore A weight tape seed N (column Q j)) < k) :
    (∫ Q in event,
      ‖(measurementSpanBefore A weight tape seed N (column Q j)).starProjection (column Q j)‖^2
        ∂orthogonalHaarProbability d) ≤ (k:ℝ)/((d:ℝ)-k+1) := by
  have heq : (fun Q : OrthogonalGroup d =>
      ‖(measurementSpanBefore A weight tape seed N (column Q j)).starProjection (column Q j)‖^2) =
      (fun Q => ‖actualCenter A weight tape seed d le_rfl N j Q‖^2) := by
    funext Q
    rw [actual_center_eq_measurement_projection A weight tape seed N le_rfl j Q]
  rw [heq]
  exact (original_event_center_energy_le A weight tape seed k hkd j event hevent hbelow).trans
    (rankPotential_le_ratio d k hkd)

#print axioms original_event_center_energy_le
#print axioms original_sphere_fiber_energy
end
end Task006.AdaptiveSphereOriginalEnergy
