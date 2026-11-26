import Bilevel.TransportControllerMachineHistory
import Bilevel.TransportControllerMachineRoundPairs

/-! Same-run paired-domain identity for the finite Borel reconstruction.
The complete conditioned frame and every preceding physical action remain
in the store used by the final fresh-angle monitor. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportNetwork TransportRound TransportEdgePosterior
set_option maxHeartbeats 800000

theorem historyMachine_domain {n D T p c m d k : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n)
    (choose : ∀ t,H × Generators n D (size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (st : H × Generators n D m)
    (L : TransportControllerPairedStore.State D k) (z : Latent n D) (t : ℕ) :
    domain (TransportControllerPairedStore.pairs
      (value (historyMachine (d := d) H e choose hc respond hr names t) ((context T hT e z,st),L) (z.2 e)).2)=
      domain (TransportControllerPairedStore.pairs L)⊔domain (runPairs hT choose respond names st z e t) := by
  induction t with
  | zero => simp only [historyMachine,value,runPairs,domain,sup_bot_eq]
  | succ t ih =>
    rw [historyMachine,value_compose,roundMachine_domain,ih,historyMachine_memory H hT]
    rw [runPairs]
    conv_rhs => rw [recordBatch_domain_old]
    exact sup_assoc _ _ _

theorem historyMachine_range {n D T p c m d k : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n)
    (choose : ∀ t,H × Generators n D (size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (st : H × Generators n D m)
    (L : TransportControllerPairedStore.State D k) (z : Latent n D) (t : ℕ) :
    range (TransportControllerPairedStore.pairs
      (value (historyMachine (d := d) H e choose hc respond hr names t) ((context T hT e z,st),L) (z.2 e)).2)=
      range (TransportControllerPairedStore.pairs L)⊔range (runPairs hT choose respond names st z e t) := by
  induction t with
  | zero => simp only [historyMachine,value,runPairs,range,sup_bot_eq]
  | succ t ih =>
    rw [historyMachine,value_compose,roundMachine_range,ih,historyMachine_memory H hT]
    rw [runPairs]
    conv_rhs => rw [recordBatch_range_old]
    exact sup_assoc _ _ _

end Bilevel.TransportControllerMachine
