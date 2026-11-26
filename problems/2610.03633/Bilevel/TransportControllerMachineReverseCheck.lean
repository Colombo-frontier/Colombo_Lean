import Bilevel.TransportControllerMachineReversePreparation
import Bilevel.TransportControllerReverseTarget

/-! Concrete reverse monitor after the real inverse replay and current
forward responses. The actual event is contained in this finite enlarged
target event; its source is exactly the actual fresh paired domain. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportNetwork TransportRound TransportEdgePosterior TransportGeneratorStore
set_option maxHeartbeats 800000

def reverseDimension (n b : ℕ) : ℕ := (b+1)+n*b

def padSource {D b : ℕ} (n : ℕ) (q : Fin b → Space D) : Fin (reverseDimension n b) → Space D :=
  Fin.append (Fin.cons 0 q) (fun _ : Fin (n*b) => 0)

theorem padSource_measurable (n D b : ℕ) : Measurable (padSource (D := D) (b := b) n) :=
  (append_measurable D (b+1) (n*b)).comp ((cons_zero_measurable D b).prodMk measurable_const)

theorem padSource_span {D b : ℕ} (n : ℕ) (q : Fin b → Space D) : span (padSource n q)=span q := by
  rw [padSource,span_append,span_cons_zero,span_zero,sup_bot_eq]

def reverseCheck {n D T m p k : ℕ} (H : Memory.{u}) (e : Edge n) (t : ℕ)
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose) :
    Machine D (reverseDimension n (m+p)) (Memory.of (RoundMemory H D T m e × (Fin (m+p) → Space D))) k
      (Memory.of (RoundMemory H D T m e × (Fin (m+p) → Space D))) k 1 := by
  let A := Memory.of (RoundMemory H D T m e × (Fin (m+p) → Space D))
  have hW : Measurable (fun s : State A D k => reverseTarget H e t choose s.1) :=
    (reverseTarget_measurable H e t choose hc).comp measurable_fst
  have hq : Measurable (fun s : State A D k => padSource n (frozenMemory H e choose s.1.1 (dst e))) :=
    (padSource_measurable n D (m+p)).comp
      (((measurable_pi_apply (dst e)).comp (frozenMemory_measurable H e choose hc)).comp (measurable_fst.comp measurable_fst))
  exact .check (fun s => reverseTarget H e t choose s.1)
    (fun s => padSource n (frozenMemory H e choose s.1.1 (dst e))) hW hq (.halt Prod.fst measurable_fst)

def reverseProgram {n D T p c m k : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : ∀ t,H × Generators n D (TransportRound.size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (TransportRound.size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (t : ℕ) :
    Machine D (reverseDimension n (TransportRound.size n p c m t+p))
      (Memory.of (RoundMemory H D T (TransportRound.size n p c m t) e ×
        (Fin (TransportRound.size n p c m t+p) → Space D)))
      (afterCount (historyCount n p c m k t) (TransportRound.size n p c m t+p)) (RoundMemory H D T m e) k
      (1+((TransportRound.size n p c m t+p)+historyProbes n p c m t)) :=
  compose (reversePreparation H e choose hc respond hr names t) (reverseCheck H e t (choose t) (hc t))

theorem reverseProgram_failure_of_actual {n D T p c m : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n)
    (choose : ∀ t,H × Generators n D (TransportRound.size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (TransportRound.size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (st : H × Generators n D m) (z : Latent n D) (t : ℕ)
    (hb : reverseMonitor hT t (frozenAt hT choose respond names st z t) z
      (fun f => runPairs hT choose respond names st z f t)
      (forwardLedger (frozenAt hT choose respond names st z t) z
        (known (postGrant T hT t (frozenAt hT choose respond names st z t) z))) e) :
    failure (reverseProgram H e choose hc respond hr names t)
      (swapState ((context T hT e z,st),frameStore e (context T hT e z))) (z.2 e)⁻¹ := by
  have hred := hb
  rw [reverseMonitor_reduced] at hred
  rw [reverseProgram,failure_compose]
  apply Or.inr
  simp only [reverseCheck,failure,or_false,TransportControllerPairedStore.fresh_span,padSource_span]
  rw [reversePreparation_memory H hT,reversePreparation_domain H hT]
  apply angleBad_target_mono (reverseTarget_contains H hT e t (choose t) (run T hT choose respond names st z t) z)
  exact hred

end Bilevel.TransportControllerMachine
