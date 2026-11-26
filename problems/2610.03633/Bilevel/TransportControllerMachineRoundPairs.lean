import Bilevel.TransportControllerMachineRound
import Bilevel.TransportControllerMachineBatchPairs
import Bilevel.TransportRoundEdgeHistory

/-! The reconstructed round has precisely the domain and range of the real
physical paired history. Array insertion order is immaterial to these spans;
no observed vector or entering paired constraint is discarded. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportNetwork TransportRound TransportEdgePosterior
set_option maxHeartbeats 800000

theorem contextBatch_domain {n D T b d m : ℕ} (H : Memory.{u}) (e : Edge n)
    (ctx : H → Context (d := D) e T) (hc : Measurable ctx)
    (g : H → Generators n D b) (hg : Measurable g) (s : State H D m) (z : Latent n D) :
    domain (TransportControllerPairedStore.pairs (value (contextBatch (d := d) H e ctx hc g hg) s (z.2 e)).2)=
      domain (TransportControllerPairedStore.pairs s.2)⊔domain (recordBatch e (g s.1) z []) := by
  rw [contextBatch_pairs,insertMany_domain,insertMany_domain]
  simp only [Bool.false_eq_true,ite_false,ite_true,batchResponse_span,recordBatch,domain_append,
    reversePairs_domain,forwardPairs_domain,domain,sup_bot_eq,known]
  simp only [sup_assoc,sup_comm,sup_left_comm]

theorem contextBatch_range {n D T b d m : ℕ} (H : Memory.{u}) (e : Edge n)
    (ctx : H → Context (d := D) e T) (hc : Measurable ctx)
    (g : H → Generators n D b) (hg : Measurable g) (s : State H D m) (z : Latent n D) :
    range (TransportControllerPairedStore.pairs (value (contextBatch (d := d) H e ctx hc g hg) s (z.2 e)).2)=
      range (TransportControllerPairedStore.pairs s.2)⊔range (recordBatch e (g s.1) z []) := by
  rw [contextBatch_pairs,insertMany_range,insertMany_range]
  simp only [Bool.false_eq_true,ite_false,ite_true,batchResponse_span,recordBatch,range_append,
    reversePairs_range,forwardPairs_range,range,sup_bot_eq,known]
  simp only [sup_assoc,sup_comm,sup_left_comm]

theorem recordBatch_domain_old {n D b : ℕ} (e : Edge n) (g : Generators n D b) (z : Latent n D) (P : Pairs D) :
    domain (recordBatch e g z P)=domain P⊔domain (recordBatch e g z []) := by
  simp only [recordBatch,domain_append,domain,sup_bot_eq]
  simp only [sup_assoc,sup_comm,sup_left_comm]

theorem recordBatch_range_old {n D b : ℕ} (e : Edge n) (g : Generators n D b) (z : Latent n D) (P : Pairs D) :
    range (recordBatch e g z P)=range P⊔range (recordBatch e g z []) := by
  simp only [recordBatch,range_append,range,sup_bot_eq]
  simp only [sup_assoc,sup_comm,sup_left_comm]

theorem roundMachine_domain {n D T m p c d k : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose)
    (respond : StepData H n D m p T → H) (hr : Measurable respond)
    (names : Vertex n → Fin c → Option (Fin T)) (s : State (RoundMemory H D T m e) D k)
    (z : Latent n D) :
    domain (TransportControllerPairedStore.pairs (value (roundMachine (d := d) H e choose hc respond hr names) s (z.2 e)).2)=
      domain (TransportControllerPairedStore.pairs s.2)⊔domain (recordBatch e (augment s.1.2.2 (choose s.1.2)) z []) := by
  simp only [roundMachine,value_map]
  exact contextBatch_domain _ _ _ _ _ _ _ _

theorem roundMachine_range {n D T m p c d k : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose)
    (respond : StepData H n D m p T → H) (hr : Measurable respond)
    (names : Vertex n → Fin c → Option (Fin T)) (s : State (RoundMemory H D T m e) D k)
    (z : Latent n D) :
    range (TransportControllerPairedStore.pairs (value (roundMachine (d := d) H e choose hc respond hr names) s (z.2 e)).2)=
      range (TransportControllerPairedStore.pairs s.2)⊔range (recordBatch e (augment s.1.2.2 (choose s.1.2)) z []) := by
  simp only [roundMachine,value_map]
  exact contextBatch_range _ _ _ _ _ _ _ _

end Bilevel.TransportControllerMachine
