import Bilevel.TransportControllerMachineForwardCheck
import Bilevel.TransportControllerMachineInverseReplay
import Bilevel.TransportControllerMachineBatchPairs

/-! Actual inverse-edge history followed by this round's frozen forward
responses. The reverse monitor is evaluated only after these responses have
entered its physical paired domain. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportNetwork TransportRound TransportEdgePosterior TransportGeneratorStore
set_option maxHeartbeats 800000

theorem batchResponse_inverse_true {D b : ℕ} (q : Fin b → Space D) (O : OrthogonalHaar.Group D) :
    batchResponse true q O⁻¹=batchResponse false q O := by
  funext i
  simp only [batchResponse,inv_inv,ite_true,Bool.false_eq_true,ite_false]

theorem swap_pairs_domain {D m : ℕ} (s : TransportControllerPairedStore.State D m) :
    domain (TransportControllerPairedStore.pairs s.swap)=range (TransportControllerPairedStore.pairs s) := by
  rw [TransportControllerPairedStore.domain_pairs,TransportControllerPairedStore.range_pairs]
  rfl

def reversePreparation {n D T p c m k d : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : ∀ t,H × Generators n D (TransportRound.size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (TransportRound.size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (t : ℕ) :
    Machine D d (Memory.of (RoundMemory H D T (TransportRound.size n p c m t) e ×
      (Fin (TransportRound.size n p c m t+p) → Space D)))
      (afterCount (historyCount n p c m k t) (TransportRound.size n p c m t+p)) (RoundMemory H D T m e) k
      ((TransportRound.size n p c m t+p)+historyProbes n p c m t) :=
  compose (inverseReplay (historyMachine H e choose hc respond hr names t))
    (collect true (TransportRound.size n p c m t+p) (historyCount n p c m k t)
      (RoundMemory H D T (TransportRound.size n p c m t) e)
      (fun s => frozenMemory H e (choose t) s (src e))
      ((measurable_pi_apply (src e)).comp (frozenMemory_measurable H e (choose t) (hc t))))

theorem reversePreparation_value {n D T p c m k d : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : ∀ t,H × Generators n D (TransportRound.size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (TransportRound.size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (t : ℕ)
    (s : State (RoundMemory H D T m e) D k) (O : OrthogonalHaar.Group D) :
    let V := value (historyMachine (d := d) H e choose hc respond hr names t) s O
    let q := frozenMemory H e (choose t) V.1 (src e)
    value (reversePreparation (d := d) H e choose hc respond hr names t) (swapState s) O⁻¹=
      ((V.1,batchResponse false q O),insertMany true V.2.swap q (batchResponse false q O)) := by
  dsimp only
  rw [reversePreparation,value_compose,value_inverseReplay_actual,collect_value,batchResponse_inverse_true]
  rfl

theorem reversePreparation_memory {n D T p c m d : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n)
    (choose : ∀ t,H × Generators n D (TransportRound.size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (TransportRound.size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (st : H × Generators n D m) (z : Latent n D) (t : ℕ) :
    (value (reversePreparation (d := d) H e choose hc respond hr names t)
      (swapState ((context T hT e z,st),frameStore e (context T hT e z))) (z.2 e)⁻¹).1=
      ((context T hT e z,run T hT choose respond names st z t),
        batchResponse false (frozenAt hT choose respond names st z t (src e)) (z.2 e)) := by
  rw [reversePreparation_value]
  simp only [historyMachine_memory H hT]
  rfl

theorem reverseHard_domain_range {n D T : ℕ} (hT : T≤D) (e : Edge n) (z : Latent n D) :
    domain (reverseHardPairs T hT e z)=range (hardPairs T hT e z) := by
  change domain (TransportControllerPairedStore.pairs (frame T hT z (dst e),frame T hT z (src e)))=
    range (TransportControllerPairedStore.pairs (frame T hT z (src e),frame T hT z (dst e)))
  rw [TransportControllerPairedStore.domain_pairs,TransportControllerPairedStore.range_pairs]

theorem reversePreparation_domain {n D T p c m d : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n)
    (choose : ∀ t,H × Generators n D (TransportRound.size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (TransportRound.size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (st : H × Generators n D m) (z : Latent n D) (t : ℕ) :
    domain (TransportControllerPairedStore.pairs
      (value (reversePreparation (d := d) H e choose hc respond hr names t)
        (swapState ((context T hT e z,st),frameStore e (context T hT e z))) (z.2 e)⁻¹).2)=
      domain (reverseHardPairs T hT e z++swapPairs (forwardPairs e (frozenAt hT choose respond names st z t) z++
        runPairs hT choose respond names st z e t)) := by
  rw [reversePreparation_value,insertMany_domain]
  simp only [ite_true,swap_pairs_domain,historyMachine_range H hT,historyMachine_memory H hT,
    frameStore_pairs hT,batchResponse_span,Bool.false_eq_true,ite_false,domain_append,reverseHard_domain_range,
    swapPairs_domain,range_append,forwardPairs_range]
  change (range (hardPairs T hT e z)⊔range (runPairs hT choose respond names st z e t))⊔
    (known (frozenAt hT choose respond names st z t) (src e)).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap=_
  simp only [sup_assoc,sup_comm,sup_left_comm]

theorem reversePreparation_no_failure {n D T p c m k d : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : ∀ t,H × Generators n D (TransportRound.size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (TransportRound.size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (t : ℕ)
    (s : State (RoundMemory H D T m e) D k) (O : OrthogonalHaar.Group D) :
    ¬failure (reversePreparation (d := d) H e choose hc respond hr names t) s O := by
  rw [reversePreparation,failure_compose]
  exact not_or.mpr ⟨inverseReplay_no_failure _ _ _,collect_no_failure _ _ _ _ _ _⟩

end Bilevel.TransportControllerMachine
