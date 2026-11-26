import Bilevel.TransportRoundMonitorMeasurable
import Bilevel.TransportRoundHorizonEnergy

/-! Joint measurable memory/instance events for the actual executed run.
Physical paired stores are derived by induction from the real frozen-batch
responses. This closes the Borel obligations of the concrete runFailure
event, without assuming its probability bound. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportEdgePosterior
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

theorem runState_joint_measurable {H : Type*} [MeasurableSpace H] {n D p T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t)) (t : ℕ) :
    Measurable (fun p : H × Latent n D => run T hT choose respond (prefixNames n T) (p.1,seed T hT p.2) p.2 t) :=
  (run_measurable T hT choose hc respond hr (prefixNames n T) t).comp
    ((measurable_fst.prodMk ((seed_measurable T hT).comp measurable_snd)).prodMk measurable_snd)

theorem frozenAt_joint_measurable {H : Type*} [MeasurableSpace H] {n D p T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t)) (t : ℕ) :
    Measurable (fun p : H × Latent n D => frozenAt hT choose respond (prefixNames n T) (p.1,seed T hT p.2) p.2 t) := by
  have hs := runState_joint_measurable hT choose hc respond hr t
  exact (augment_measurable n D (size n p 1 1 t) p).comp
    ((measurable_snd.comp hs).prodMk ((hc t).comp hs))

theorem runPairs_projector_measurable {H : Type*} [MeasurableSpace H] {n D p T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t)) (t : ℕ) :
    (∀ e,Measurable (fun p : H × Latent n D => ProjectionStore.ofSubspace D
      (domain (runPairs hT choose respond (prefixNames n T) (p.1,seed T hT p.2) p.2 e t)))) ∧
    (∀ e,Measurable (fun p : H × Latent n D => ProjectionStore.ofSubspace D
      (range (runPairs hT choose respond (prefixNames n T) (p.1,seed T hT p.2) p.2 e t)))) := by
  induction t with
  | zero =>
    constructor <;> intro e <;> simp only [runPairs] <;> exact measurable_const
  | succ t ih =>
    have hg := frozenAt_joint_measurable hT choose hc respond hr t
    constructor
    · intro e
      have hsrc := known_projector_measurable _ hg (src e)
      have hdst := known_projector_measurable _ hg (dst e)
      have hO : Measurable (fun p : H × Latent n D => (p.2.2 e)⁻¹) :=
        ((measurable_pi_apply e).comp (measurable_snd.comp measurable_snd)).inv
      have hm := map_projector_measurable _ hdst _ hO
      have hh := sup_projector_measurable _ _ (sup_projector_measurable _ _ hm hsrc) (ih.1 e)
      simpa only [runPairs,recordBatch,domain_append,reversePairs_domain,forwardPairs_domain,frozenAt] using hh
    · intro e
      have hsrc := known_projector_measurable _ hg (src e)
      have hdst := known_projector_measurable _ hg (dst e)
      have hO : Measurable (fun p : H × Latent n D => p.2.2 e) :=
        (measurable_pi_apply e).comp (measurable_snd.comp measurable_snd)
      have hm := map_projector_measurable _ hsrc _ hO
      have hh := sup_projector_measurable _ _ (sup_projector_measurable _ _ hdst hm) (ih.2 e)
      simpa only [runPairs,recordBatch,range_append,reversePairs_range,forwardPairs_range,frozenAt] using hh

theorem runFailure_measurable {H : Type*} [MeasurableSpace H] {n D p T : ℕ} (hT : T≤D) (a : ℝ)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t)) (t : ℕ) :
    MeasurableSet {p : H × Latent n D | runFailure hT a choose respond p.1 p.2 t} := by
  have hs := runState_joint_measurable hT choose hc respond hr t
  have hg := frozenAt_joint_measurable hT choose hc respond hr t
  have hP := runPairs_projector_measurable hT choose hc respond hr t
  exact (requests_bad_joint_measurable hT a _ (measurable_snd.comp hs) _ ((hc t).comp hs) _ measurable_snd).union
    (batchFailure_measurable hT t _ hg _ measurable_snd _ hP.1 hP.2)

theorem runEnergy_joint_measurable {H : Type*} [MeasurableSpace H] {n D p T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t)) (t : ℕ) :
    Measurable (fun p : H × Latent n D => runEnergy hT choose respond p.1 p.2 t) := by
  have hs := runState_joint_measurable hT choose hc respond hr t
  exact generator_ledger_measurable D (size n p 1 1 t) T (n+1)
    _ (measurable_snd.comp hs) _ ((frame_measurable n D T hT).comp measurable_snd) (oldFuture T t)

def runFailureEvent {H : Type*} {n D p T : ℕ} (hT : T≤D) (a : ℝ)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H) (M : ℕ) : Set (H × Latent n D) :=
  {p | ∃ t<M,runFailure hT a choose respond p.1 p.2 t}

theorem runFailureEvent_measurable {H : Type*} [MeasurableSpace H] {n D p T : ℕ} (hT : T≤D) (a : ℝ)
    (choose : ∀ t, H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t)) (M : ℕ) :
    MeasurableSet (runFailureEvent hT a choose respond M) := by
  have he : runFailureEvent hT a choose respond M=
      ⋃ t : ℕ,⋃ (_ : t<M),{p : H × Latent n D | runFailure hT a choose respond p.1 p.2 t} := by
    ext p
    simp [runFailureEvent]
  rw [he]
  exact MeasurableSet.iUnion (fun t => MeasurableSet.iUnion (fun _ => runFailure_measurable hT a choose hc respond hr t))

end Bilevel.TransportRound
