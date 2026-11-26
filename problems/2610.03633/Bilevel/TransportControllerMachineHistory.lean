import Bilevel.TransportControllerMachineRound
import Bilevel.TransportControllerHistory

/-! The original adaptive finite run is reconstructed by a single Borel
machine. Each successive round receives the previous actual memory and
generators, and the same original paired history is carried throughout. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportNetwork TransportRound
set_option maxHeartbeats 800000

def historyCount (n p c m k : ℕ) : ℕ → ℕ
  | 0 => k
  | t+1 => bothCount (historyCount n p c m k t) (size n p c m t+p)

def historyProbes (n p c m : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => (size n p c m t+p)+(size n p c m t+p)+historyProbes n p c m t

theorem historyCount_eq (n p c m k t : ℕ) : historyCount n p c m k t=k+historyProbes n p c m t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [historyCount,bothCount_eq,ih,historyProbes]; omega

theorem historyProbes_le_historySize {n : ℕ} (hn : 0<n) (p c m t : ℕ) :
    historyProbes n p c m t≤historySize n p c m t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    have hm : size n p c m t+p≤n*(size n p c m t+p) := by
      simpa using Nat.mul_le_mul_right (size n p c m t+p) (show 1≤n from hn)
    simp only [historyProbes,historySize]
    omega

def historyMachine {n D T p c m d k : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : ∀ t,H × Generators n D (size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) :
    (t : ℕ) → Machine D d (RoundMemory H D T (size n p c m t) e) (historyCount n p c m k t)
      (RoundMemory H D T m e) k (historyProbes n p c m t)
  | 0 => .halt Prod.fst measurable_fst
  | t+1 => compose (historyMachine H e choose hc respond hr names t)
      (roundMachine H e (choose t) (hc t) (respond t) (hr t) (names t))

theorem historyMachine_memory {n D T p c m d k : ℕ} (H : Memory.{u}) (hT : T≤D) (e : Edge n)
    (choose : ∀ t,H × Generators n D (size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) (st : H × Generators n D m)
    (L : TransportControllerPairedStore.State D k) (z : Latent n D) (t : ℕ) :
    (value (historyMachine (d := d) H e choose hc respond hr names t) ((context T hT e z,st),L) (z.2 e)).1=
      (context T hT e z,run T hT choose respond names st z t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [historyMachine,value_compose]
    have he : value (historyMachine (d := d) H e choose hc respond hr names t) ((context T hT e z,st),L) (z.2 e)=
        ((context T hT e z,run T hT choose respond names st z t),
          (value (historyMachine (d := d) H e choose hc respond hr names t) ((context T hT e z,st),L) (z.2 e)).2) :=
      Prod.ext ih rfl
    rw [he,roundMachine_memory H hT]
    rfl

theorem historyMachine_no_failure {n D T p c m d k : ℕ} (H : Memory.{u}) (e : Edge n)
    (choose : ∀ t,H × Generators n D (size n p c m t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p c m t) p T → H) (hr : ∀ t,Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : State (RoundMemory H D T m e) D k) (O : OrthogonalHaar.Group D) (t : ℕ) :
    ¬failure (historyMachine (d := d) H e choose hc respond hr names t) s O := by
  induction t with
  | zero => exact not_false
  | succ t ih =>
    rw [historyMachine,failure_compose]
    exact not_or.mpr ⟨ih,roundMachine_no_failure _ _ _ _ _ _ _ _ _⟩

end Bilevel.TransportControllerMachine
