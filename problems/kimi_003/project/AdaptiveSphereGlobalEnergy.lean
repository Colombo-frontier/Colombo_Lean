import AdaptiveSphereStoppedEnergy
import AdaptiveSphereGlobalMean

/-! The actual spherical stopped-energy bound with arbitrary independent
exogenous private-seed/sample-tape distribution. Fubini integrates the fully
proved fixed-parameter adaptive energy theorem. -/
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Task006.AdaptiveSphereGlobal
open Task006.Full Task006.Full.OracleAlgorithm Task006.HaarRebalancing
open Task006.AdaptiveSphereState Task006.AdaptiveSphereStopped Task006.AdaptiveSphereAction
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereTranscript Task006.PosteriorCenter
open Task006.AdaptiveSphereJoint Task006.AdaptiveSphereMean Task006.AdaptiveSphere
open Task006.AdaptiveSphereStoppedEnergy Task006.StoppedEnergy
noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

theorem joint_center_energy_integrable (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (t : ℕ) (ht : t ≤ N) (j : Fin d)
    (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ] :
    Integrable (fun w => ‖jointCenter A k hkd t j w‖^2) (γ.prod (orthogonalHaarProbability d)) := by
  have hC := (jointCenter_stronglyMeasurable_past A k hkd t j).mono
    (jointObservation_measurable A k hkd t j).comap_le
  have hm : Measurable (fun w => ‖jointCenter A k hkd t j w‖^2) := hC.measurable.norm.pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro w
  have h := jointCenter_norm_le_one A k hkd t ht j w
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg (jointCenter A k hkd t j w)]

/-- Unconditional stopped posterior energy for an arbitrary independent
exogenous law. Its conclusion is derived from the real adaptive transcript. -/
theorem joint_expected_center_energy_le (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (j : Fin d) (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ] :
    (∫ w, ‖jointCenter A k hkd N j w‖^2 ∂γ.prod (orthogonalHaarProbability d)) ≤
      rankPotential d k := by
  have hint := joint_center_energy_integrable A k hkd N le_rfl j γ
  rw [integral_prod _ hint]
  calc
    _ ≤ ∫ _z : Exogenous S, rankPotential d k ∂γ := by
      apply integral_mono hint.integral_prod_left (integrable_const _)
      intro z
      have heq : (fun Q : OrthogonalGroup d => ‖jointCenter A k hkd N j (z,Q)‖^2) =
          (fun Q => ‖actualCenter (stoppedObserver A id z.2 z.1 k hkd) id z.2 () k hkd N j Q‖^2) := by
        funext Q
        rw [jointCenter_eq_fixed]
      change (∫ Q : OrthogonalGroup d, ‖jointCenter A k hkd N j (z,Q)‖^2
        ∂orthogonalHaarProbability d) ≤ rankPotential d k
      rw [heq]
      exact stoppedObserver_expected_center_energy_le A id z.2 z.1 k hkd j
    _ = _ := by simp

/-- Restriction to an arbitrary measurable event cannot increase the actual
nonnegative stopped energy. No event-energy premise is assumed. -/
theorem joint_event_center_energy_le (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (j : Fin d) (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ]
    (event : Set (Exogenous S × OrthogonalGroup d)) :
    (∫ w in event, ‖jointCenter A k hkd N j w‖^2 ∂γ.prod (orthogonalHaarProbability d)) ≤
      rankPotential d k := by
  exact (setIntegral_le_integral (joint_center_energy_integrable A k hkd N le_rfl j γ)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).trans
      (joint_expected_center_energy_le A k hkd j γ)

/-- The finite harmonic potential gives the precise stopped-rank ratio used in
both the small- and large-dimensional lower-bound arguments. -/
theorem joint_event_center_energy_le_ratio (A : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d)
    (j : Fin d) (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ]
    (event : Set (Exogenous S × OrthogonalGroup d)) :
    (∫ w in event, ‖jointCenter A k hkd N j w‖^2 ∂γ.prod (orthogonalHaarProbability d)) ≤
      (k:ℝ)/((d:ℝ)-k+1) :=
  (joint_event_center_energy_le A k hkd j γ event).trans (rankPotential_le_ratio d k hkd)

#print axioms joint_center_energy_integrable
#print axioms joint_expected_center_energy_le
#print axioms joint_event_center_energy_le
#print axioms joint_event_center_energy_le_ratio
end
end Task006.AdaptiveSphereGlobal
