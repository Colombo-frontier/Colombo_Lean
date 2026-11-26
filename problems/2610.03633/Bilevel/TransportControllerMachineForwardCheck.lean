import Bilevel.TransportControllerMachineHistoryPairs
import Bilevel.TransportRoundDistinctTargets

/-! A concrete terminal forward monitor after reconstruction of the actual
adaptive history. Its finite target and source arrays have length m+p+1,
independent of ambient dimension. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportNetwork TransportRound TransportEdgePosterior TransportGeneratorStore
set_option maxHeartbeats 800000

def frozenMemory {n D T m p : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : H × Generators n D m → Queries n D p) (s : RoundMemory H D T m e) : Generators n D (m+p) :=
  augment s.2.2 (choose s.2)

theorem frozenMemory_measurable {n D T m p : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose) : Measurable (frozenMemory (T := T) H e choose) :=
  (augment_measurable n D m p).comp ((measurable_snd.comp measurable_snd).prodMk (hc.comp measurable_snd))

def grantMemory {n D T m p : ℕ} (H : Memory.{u}) (e : Edge n) (t : ℕ)
    (choose : H × Generators n D m → Queries n D p) (s : RoundMemory H D T m e) : Generators n D ((m+p)+1) :=
  augment (frozenMemory H e choose s) (contextDisclosures s.1 (fun v (_ : Fin 1) => postNew t v))

theorem grantMemory_measurable {n D T m p : ℕ} (H : Memory.{u}) (e : Edge n) (t : ℕ)
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose) : Measurable (grantMemory (T := T) H e t choose) :=
  (augment_measurable n D (m+p) 1).comp ((frozenMemory_measurable H e choose hc).prodMk
    ((contextDisclosures_measurable e (fun v (_ : Fin 1) => postNew t v)).comp measurable_fst))

theorem cons_zero_measurable (D b : ℕ) :
    Measurable (fun v : Fin b → Space D => (Fin.cons (0 : Space D) v : Fin (b+1) → Space D)) := by
  apply measurable_pi_lambda
  intro i
  cases i using Fin.cases with
  | zero => exact measurable_const
  | succ i => exact measurable_pi_apply i

theorem span_cons_zero {D b : ℕ} (v : Fin b → Space D) : span (Fin.cons (0 : Space D) v)=span v := by
  rw [span_cons,Submodule.span_zero_singleton,sup_bot_eq]

def forwardCheck {n D T m p k : ℕ} (H : Memory.{u}) (e : Edge n) (t : ℕ)
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose) :
    Machine D ((m+p)+1) (RoundMemory H D T m e) k (RoundMemory H D T m e) k 1 :=
  .check (fun s => grantMemory H e t choose s.1 (dst e))
    (fun s => Fin.cons 0 (frozenMemory H e choose s.1 (src e)))
    (((measurable_pi_apply (dst e)).comp (grantMemory_measurable H e t choose hc)).comp measurable_fst)
    ((cons_zero_measurable D (m+p)).comp
      (((measurable_pi_apply (src e)).comp (frozenMemory_measurable H e choose hc)).comp measurable_fst))
    (.halt Prod.fst measurable_fst)

def forwardProgram {n D T p c m k : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : ∀ t,H × Generators n D (TransportRound.size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (TransportRound.size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (t : ℕ) :
    Machine D ((TransportRound.size n p c m t+p)+1) (RoundMemory H D T (TransportRound.size n p c m t) e)
      (historyCount n p c m k t) (RoundMemory H D T m e) k (1+historyProbes n p c m t) :=
  compose (historyMachine H e choose hc respond hr names t) (forwardCheck H e t (choose t) (hc t))

def frameStore {n D T : ℕ} (e : Edge n) (ctx : Context (d := D) e T) : TransportControllerPairedStore.State D T :=
  (ctx.1 (src e),ctx.1 (dst e))

theorem frameStore_pairs {n D T : ℕ} (hT : T≤D) (e : Edge n) (z : Latent n D) :
    TransportControllerPairedStore.pairs (frameStore e (context T hT e z))=hardPairs T hT e z := rfl

theorem forwardProgram_failure {n D T p c m : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n)
    (choose : ∀ t,H × Generators n D (TransportRound.size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (TransportRound.size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (st : H × Generators n D m) (z : Latent n D) (t : ℕ) :
    failure (forwardProgram H e choose hc respond hr names t)
      ((context T hT e z,st),frameStore e (context T hT e z)) (z.2 e) ↔
      forwardMonitor hT t (frozenAt hT choose respond names st z t) z
        (fun f => runPairs hT choose respond names st z f t)
        (known (postGrant T hT t (frozenAt hT choose respond names st z t) z)) e := by
  rw [forwardProgram,failure_compose]
  have hn := historyMachine_no_failure (d := (TransportRound.size n p c m t+p)+1) H e choose hc respond hr names
    ((context T hT e z,st),frameStore e (context T hT e z)) (z.2 e) t
  rw [show failure (historyMachine (d := (TransportRound.size n p c m t+p)+1) H e choose hc respond hr names t)
      ((context T hT e z,st),frameStore e (context T hT e z)) (z.2 e) ↔ False from iff_false_intro hn]
  simp only [false_or,forwardCheck,failure,or_false,TransportControllerPairedStore.fresh_span,span_cons_zero]
  rw [historyMachine_memory H hT,historyMachine_domain H hT,frameStore_pairs hT,← domain_append]
  rw [forwardMonitor_reduced]
  rfl

end Bilevel.TransportControllerMachine
