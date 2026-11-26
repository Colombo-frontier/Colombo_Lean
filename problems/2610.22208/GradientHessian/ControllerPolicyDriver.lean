import GradientHessian.ComparisonControllerReplay
import GradientHessian.ComparisonControllerPhases
import GradientHessian.Machine

/-! A literal chronological driver. Policy instructions, repair steps,
normal operations and reply delivery have separate transitions. A pending
query keeps its policy state and physical point throughout repair. The
finite policy cutoff appends exactly one virtual ordinary output operation.

Replay requires equality of actual predicates and reply functions only
before disclosure; it does not assume independence or oracle correctness. -/

noncomputable section
namespace GradientHessian.ControllerPolicyDriver

open Classical FrontierState TaskState TaskSlots ComparisonController
open ComparisonControllerReplay

variable {L M ell : ℕ} {Seed S X Y Z Action : Type*}

inductive Config (L M ell : ℕ) (S X Action : Type*) where
  | ready (remaining : ℕ) (algorithm : S) (controller : State L M ell)
  | pending (remaining : ℕ) (algorithm : S) (output : Bool)
      (phase : Phase L M ell X Action)
  | finished (algorithm : S) (controller : State L M ell)

variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

/-- Delivery is guarded on both snapshots. In particular, a normal
completion that supplies the erased datum is frozen before any reply. -/
def deliver (P : Machine.Policy Seed S X Y Z) (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (output : Bool) (p : Pending X)
    (before after : State L M ell) : Config L M ell S X Action :=
  if stop before || stop after then .finished a after
  else if output then .finished a after
  else match p.kind with
    | .ordinary => .ready (n-1) (P.ordinaryNext (a,ordinary before after p.point)) after
    | .rich => .ready (n-1) (P.richNext (a,rich before after p.point)) after

def step (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X Action)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z) :
    Config L M ell S X Action → Config L M ell S X Action
  | .ready n a s =>
    if stop s then .finished a s
    else if n=0 ∨ P.mode a=0 then
      .pending n a true (.repairing ⟨P.output a,.ordinary⟩ s)
    else if P.mode a=1 then .ready (n-1) (P.think a) s
    else .pending n a false (.repairing ⟨P.point a,if P.mode a=2 then .ordinary else .rich⟩ s)
  | .pending n a output q => match q with
    | .frozen _ s => .finished a s
    | .delivered p before after => deliver P stop ordinary rich n a output p before after
    | .repairing _ _ | .normal _ _ => .pending n a output (guardedTick R stop q)
  | .finished a s => .finished a s

def run (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X Action)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z) :
    ℕ → Config L M ell S X Action → Config L M ell S X Action
  | 0,q => q
  | n+1,q => run P R stop ordinary rich n (step P R stop ordinary rich q)

def initial (P : Machine.Policy Seed S X Y Z) (N : ℕ) (seed : Seed)
    (s : State L M ell) : Config L M ell S X Action := .ready N (P.initial seed) s

@[simp] theorem run_finished (P : Machine.Policy Seed S X Y Z)
    (R : Rules L M ell X Action) (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (s : State L M ell) :
    run P R stop ordinary rich n (.finished a s)=.finished a s := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem run_add (P : Machine.Policy Seed S X Y Z)
    (R : Rules L M ell X Action) (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n k : ℕ) (q : Config L M ell S X Action) :
    run P R stop ordinary rich (n+k) q=
      run P R stop ordinary rich k (run P R stop ordinary rich n q) := by
  induction n generalizing q with
  | zero => simp only [Nat.zero_add,run]
  | succ n ih => simpa only [Nat.succ_add,run] using ih (step P R stop ordinary rich q)

theorem deliver_congr (P : Machine.Policy Seed S X Y Z) (stop : State L M ell → Bool)
    (o₁ o₂ : State L M ell → State L M ell → X → Y)
    (r₁ r₂ : State L M ell → State L M ell → X → Z)
    (ho : ∀ b a,stop b=false → stop a=false → ∀ x,o₁ b a x=o₂ b a x)
    (hr : ∀ b a,stop b=false → stop a=false → ∀ x,r₁ b a x=r₂ b a x)
    (n : ℕ) (a : S) (output : Bool) (p : Pending X)
    (before after : State L M ell) :
    deliver (Action := Action) P stop o₁ r₁ n a output p before after=
      deliver P stop o₂ r₂ n a output p before after := by
  cases hb : stop before <;> cases ha : stop after
  · simp only [deliver,hb,ha,Bool.or_false,Bool.false_eq_true,if_false]
    cases output <;> cases hk : p.kind <;> simp [hk,ho before after hb ha,hr before after hb ha]
  all_goals simp [deliver,hb,ha]

theorem step_congr (P : Machine.Policy Seed S X Y Z) (R T : Rules L M ell X Action)
    (stop : State L M ell → Bool)
    (hp : R.priority=T.priority) (ht : R.target=T.target)
    (htrigger : ∀ s,stop s=false → ∀ x a,R.trigger s x a=T.trigger s x a)
    (hhit : ∀ s,stop s=false → ∀ x,R.hit s x=T.hit s x)
    (o₁ o₂ : State L M ell → State L M ell → X → Y)
    (r₁ r₂ : State L M ell → State L M ell → X → Z)
    (ho : ∀ b a,stop b=false → stop a=false → ∀ x,o₁ b a x=o₂ b a x)
    (hr : ∀ b a,stop b=false → stop a=false → ∀ x,r₁ b a x=r₂ b a x)
    (q : Config L M ell S X Action) :
    step P R stop o₁ r₁ q=step P T stop o₂ r₂ q := by
  cases q with
  | ready n a s => rfl
  | finished a s => rfl
  | pending n a output phase =>
    cases phase with
    | repairing p s =>
      exact congrArg (Config.pending n a output)
        (guardedTick_congr R T stop hp ht htrigger hhit (.repairing p s))
    | normal p s =>
      exact congrArg (Config.pending n a output)
        (guardedTick_congr R T stop hp ht htrigger hhit (.normal p s))
    | frozen p s => rfl
    | delivered p before after => exact deliver_congr P stop o₁ o₂ r₁ r₂ ho hr n a output p before after

/-- Equality holds for every finite internal time and the entire saved
configuration, hence also for each subsequently selected query or output. -/
theorem run_congr (P : Machine.Policy Seed S X Y Z) (R T : Rules L M ell X Action)
    (stop : State L M ell → Bool)
    (hp : R.priority=T.priority) (ht : R.target=T.target)
    (htrigger : ∀ s,stop s=false → ∀ x a,R.trigger s x a=T.trigger s x a)
    (hhit : ∀ s,stop s=false → ∀ x,R.hit s x=T.hit s x)
    (o₁ o₂ : State L M ell → State L M ell → X → Y)
    (r₁ r₂ : State L M ell → State L M ell → X → Z)
    (ho : ∀ b a,stop b=false → stop a=false → ∀ x,o₁ b a x=o₂ b a x)
    (hr : ∀ b a,stop b=false → stop a=false → ∀ x,r₁ b a x=r₂ b a x)
    (n : ℕ) (q : Config L M ell S X Action) :
    run P R stop o₁ r₁ n q=run P T stop o₂ r₂ n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [run,step_congr P R T stop hp ht htrigger hhit o₁ o₂ r₁ r₂ ho hr,ih]

/-- A repair or normal step neither changes the saved policy state nor
selects a new physical point. -/
theorem repairing_step (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X Action)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (output : Bool) (p : Pending X) (s : State L M ell) :
    step P R stop ordinary rich (.pending n a output (.repairing p s))=
      .pending n a output (guardedTick R stop (.repairing p s)) ∧
    point (guardedTick R stop (.repairing p s))=p.point := ⟨rfl,guardedTick_point ..⟩

theorem stopped_before_reply (P : Machine.Policy Seed S X Y Z)
    (R : Rules L M ell X Action) (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (output : Bool) (p : Pending X) (before after : State L M ell)
    (ha : stop after=true) :
    step P R stop ordinary rich (.pending n a output (.delivered p before after))=
      .finished a after := by simp [step,deliver,ha]

/-- The unguarded internal execution realizes the literal repair receipt,
without consuming a policy instruction during repair or normal processing. -/
theorem repair_execution (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X Action)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (output : Bool) (p : Pending X)
    (fuel : ℕ) (s : State L M ell)
    (hf : (unretired (TaskState.retired s)).card ≤ fuel) :
    run P R (fun _ => false) ordinary rich ((repairRun R p fuel s).2.length+2)
      (.pending n a output (.repairing p s))=
      .pending n a output (.delivered p (repairRun R p fuel s).1
        (normal R p (repairRun R p fuel s).1)) := by
  induction fuel generalizing s with
  | zero =>
    have hc := repairRun_terminal R p 0 s hf
    change choose R p s=none at hc
    simp [repairRun,run,step,guardedTick,freeze,tick,hc]
  | succ fuel ih =>
    cases hc : choose R p s with
    | none => simp [repairRun,run,step,guardedTick,freeze,tick,hc]
    | some b =>
      have hp := retirement_progress (TaskState.retired s) (R.target b) (choose_spec R p s hc).2.2
      have hb : (unretired (TaskState.retired (retireNode s (R.target b)))).card ≤ fuel := by
        rw [retireNode_retired]
        omega
      simpa only [repairRun,hc,List.length_cons,Nat.add_right_comm,run,step,guardedTick,
        freeze,Bool.false_eq_true,if_false,tick] using ih (retireNode s (R.target b)) hb

theorem serve_execution (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X Action)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (output : Bool) (p : Pending X) (s : State L M ell) :
    run P R (fun _ => false) ordinary rich ((serve R p s).repairs.length+2)
      (.pending n a output (.repairing p s))=
      .pending n a output (.delivered p (serve R p s).beforeNormal (serve R p s).afterNormal) :=
  repair_execution P R ordinary rich n a output p (8^L) s
    ((Finset.card_le_univ _).trans_eq (leaf_card L))

/-- Including delivery takes exactly one more transition. In particular,
normal processing is not rerun on the next current leaf at this point. -/
theorem serve_delivery (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X Action)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (output : Bool) (p : Pending X) (s : State L M ell) :
    run P R (fun _ => false) ordinary rich ((serve R p s).repairs.length+3)
      (.pending n a output (.repairing p s))=
      deliver P (fun _ => false) ordinary rich n a output p
        (serve R p s).beforeNormal (serve R p s).afterNormal := by
  rw [show (serve R p s).repairs.length+3=(serve R p s).repairs.length+2+1 by omega,
    run_add,serve_execution]
  rfl

/-- A selection is emitted only when the policy chooses a new point;
internal repair and reply delivery emit none. -/
def selected (P : Machine.Policy Seed S X Y Z) (stop : State L M ell → Bool) :
    Config L M ell S X Action → Option (Pending X)
  | .ready n a s =>
    if stop s then none
    else if n=0 ∨ P.mode a=0 then some ⟨P.output a,.ordinary⟩
    else if P.mode a=1 then none
    else some ⟨P.point a,if P.mode a=2 then .ordinary else .rich⟩
  | .pending _ _ _ _ | .finished _ _ => none

def selections (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X Action)
    (stop : State L M ell → Bool)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (fuel : ℕ) (q : Config L M ell S X Action) : List (Pending X) :=
  (List.range fuel).filterMap (fun i => selected P stop (run P R stop ordinary rich i q))

theorem selections_congr (P : Machine.Policy Seed S X Y Z) (R T : Rules L M ell X Action)
    (stop : State L M ell → Bool)
    (hp : R.priority=T.priority) (ht : R.target=T.target)
    (htrigger : ∀ s,stop s=false → ∀ x a,R.trigger s x a=T.trigger s x a)
    (hhit : ∀ s,stop s=false → ∀ x,R.hit s x=T.hit s x)
    (o₁ o₂ : State L M ell → State L M ell → X → Y)
    (r₁ r₂ : State L M ell → State L M ell → X → Z)
    (ho : ∀ b a,stop b=false → stop a=false → ∀ x,o₁ b a x=o₂ b a x)
    (hr : ∀ b a,stop b=false → stop a=false → ∀ x,r₁ b a x=r₂ b a x)
    (fuel : ℕ) (q : Config L M ell S X Action) :
    selections P R stop o₁ r₁ fuel q=selections P T stop o₂ r₂ fuel q := by
  unfold selections
  congr 1
  funext i
  rw [run_congr P R T stop hp ht htrigger hhit o₁ o₂ r₁ r₂ ho hr]

end GradientHessian.ControllerPolicyDriver
