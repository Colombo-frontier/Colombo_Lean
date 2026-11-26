import Bilevel.TransportControllerMachineCompose

/-! Concrete finite frozen-input batches for the heterogeneous machine.
Every request is evaluated from the initial batch memory; previously returned
vectors are collected only as outputs. The original paired store is retained. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.TransportControllerMachine
open EuclideanGaussian OrthogonalAction TransportGeneratorStore TransportEdgePosterior
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

def afterCount (m : ℕ) : ℕ → ℕ
  | 0 => m
  | b+1 => afterCount (m+1) b

theorem afterCount_eq (m b : ℕ) : afterCount m b=m+b := by
  induction b generalizing m with
  | zero => rfl
  | succ b ih => rw [afterCount,ih]; omega

def insertMany {D : ℕ} (rev : Bool) : {b m : ℕ} → TransportControllerPairedStore.State D m →
    (Fin b → Space D) → (Fin b → Space D) → TransportControllerPairedStore.State D (afterCount m b)
  | 0,_,s,_,_ => s
  | b+1,m,s,q,y => insertMany (b := b) (m := m+1) rev
      (if rev then TransportControllerPairedStore.insert s (y 0) (q 0)
        else TransportControllerPairedStore.insert s (q 0) (y 0))
      (fun i => q i.succ) (fun i => y i.succ)

def batchResponse {D b : ℕ} (rev : Bool) (q : Fin b → Space D) (O : OrthogonalHaar.Group D) :
    Fin b → Space D := fun i => if rev then O⁻¹ • q i else O • q i

def restore {H : Memory.{u}} {D b : ℕ} (p : (H × Space D) × (Fin b → Space D)) :
    H × (Fin (b+1) → Space D) := (p.1.1,Fin.cons p.1.2 p.2)

theorem restore_measurable (H : Memory.{u}) (D b : ℕ) : Measurable (restore (H := H) (D := D) (b := b)) := by
  apply Measurable.prodMk (measurable_fst.comp measurable_fst)
  apply measurable_pi_lambda
  intro i
  cases i using Fin.cases with
  | zero => exact measurable_snd.comp measurable_fst
  | succ i => exact (measurable_pi_apply i).comp measurable_snd

def collect {D d : ℕ} (rev : Bool) : (b m : ℕ) → (H : Memory.{u}) →
    (q : H → Fin b → Space D) → Measurable q →
    Machine D d (Memory.of (H × (Fin b → Space D))) (afterCount m b) H m b
  | 0,m,H,_,_ => .halt (fun s => (s.1,Fin.elim0)) (measurable_fst.prodMk measurable_const)
  | b+1,m,H,q,hq => by
    let qt : H × Space D → Fin b → Space D := fun p i => q p.1 i.succ
    have hqt : Measurable qt := measurable_pi_lambda _
      (fun i => (measurable_pi_apply i.succ).comp (hq.comp measurable_fst))
    let next := map (d := d) (C := Memory.of (H × (Fin (b+1) → Space D)))
      (collect (d := d) rev b (m+1) (Memory.of (H × Space D)) qt hqt)
      (restore (H := H) (D := D) (b := b)) (restore_measurable H D b)
    have hfirst : Measurable (fun s : State H D m => q s.1 0) :=
      (measurable_pi_apply 0).comp (hq.comp measurable_fst)
    have hkeep : Measurable (fun p : State H D m × Space D => (p.1.1,p.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    exact if rev then .reverse (fun s => q s.1 0) hfirst (fun p => (p.1.1,p.2)) hkeep next
      else .forward (fun s => q s.1 0) hfirst (fun p => (p.1.1,p.2)) hkeep next

theorem collect_value {D d b m : ℕ} (rev : Bool) (H : Memory.{u})
    (q : H → Fin b → Space D) (hq : Measurable q) (s : State H D m) (O : OrthogonalHaar.Group D) :
    value (collect (d := d) rev b m H q hq) s O =
      ((s.1,batchResponse rev (q s.1) O),insertMany rev s.2 (q s.1) (batchResponse rev (q s.1) O)) := by
  induction b generalizing m H with
  | zero =>
    dsimp only [collect,value,insertMany]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        exact Fin.elim0 i
    · rfl
  | succ b ih =>
    cases rev with
    | false =>
      simp only [collect,Bool.false_eq_true,ite_false,value,value_map]
      rw [ih]
      dsimp only [restore,forwardState]
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext i
          cases i using Fin.cases <;> rfl
      · rfl
    | true =>
      simp only [collect,ite_true,value,value_map]
      rw [ih]
      dsimp only [restore,reverseState]
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext i
          cases i using Fin.cases <;> rfl
      · rfl

theorem collect_no_failure {D d b m : ℕ} (rev : Bool) (H : Memory.{u})
    (q : H → Fin b → Space D) (hq : Measurable q) (s : State H D m) (O : OrthogonalHaar.Group D) :
    ¬ failure (collect (d := d) rev b m H q hq) s O := by
  induction b generalizing m H with
  | zero => exact not_false
  | succ b ih =>
    cases rev with
    | false => simpa only [collect,Bool.false_eq_true,ite_false,failure,failure_map] using ih _ _ _ _
    | true => simpa only [collect,ite_true,failure,failure_map] using ih _ _ _ _

end Bilevel.TransportControllerMachine
