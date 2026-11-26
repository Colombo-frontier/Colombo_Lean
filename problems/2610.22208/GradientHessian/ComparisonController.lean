import GradientHessian.TaskSlots

/-!
# A chronological comparison controller

The selected point and query kind are fixed before any repair. Repairs retire
genuine subtrees, and a terminal repair pass is followed by exactly one normal
operation. The receipt retains the pre-normal frontier for assembling that
same reply. Geometric predicates and jet decoders are not asserted here.
-/

noncomputable section
namespace GradientHessian.ComparisonController

open Classical FrontierState TaskState TaskSlots

inductive Kind where
  | ordinary
  | rich
  deriving DecidableEq

@[ext] structure Pending (X : Type*) where
  point : X
  kind : Kind

structure Rules (L M ell : ℕ) (X Action : Type*) where
  priority : List Action
  target : Action → Node L
  trigger : State L M ell → X → Action → Bool
  hit : State L M ell → X → Bool

variable {L M ell : ℕ} {X Action : Type*}

def choose (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) : Option Action :=
  R.priority.find? fun a => R.trigger s p.point a &&
    decide ((subtree (R.target a) \ TaskState.retired s).Nonempty)

theorem choose_spec (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell)
    {a : Action} (ha : choose R p s = some a) :
    a ∈ R.priority ∧ R.trigger s p.point a = true ∧
      (subtree (R.target a) \ TaskState.retired s).Nonempty := by
  refine ⟨List.mem_of_find?_eq_some ha,?_⟩
  simpa only [Bool.and_eq_true,decide_eq_true_eq] using (List.find?_some ha)

theorem choose_none_iff (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) :
    choose R p s = none ↔ ∀ a ∈ R.priority, R.trigger s p.point a = true →
      subtree (R.target a) ⊆ TaskState.retired s := by
  exact FrontierState.chooseRepair_none_iff R.priority R.target
    (fun _ a => R.trigger s p.point a) (TaskState.retired s)

/-- The trace stores the actual state immediately before each repair. -/
def repairRun (R : Rules L M ell X Action) (p : Pending X) :
    ℕ → State L M ell → State L M ell × List (State L M ell × Action)
  | 0,s => (s,[])
  | n+1,s => match choose R p s with
    | none => (s,[])
    | some a =>
      let out := repairRun R p n (retireNode s (R.target a))
      (out.1,(s,a)::out.2)

def visits (R : Rules L M ell X Action) (p : Pending X) (n : ℕ) (s : State L M ell) :
    List (State L M ell) :=
  (repairRun R p n s).2.map Prod.fst ++ [(repairRun R p n s).1]

theorem repairRun_retired_mono (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) (s : State L M ell) :
    TaskState.retired s ⊆ TaskState.retired (repairRun R p n s).1 := by
  induction n generalizing s with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
    cases hc : choose R p s with
    | none => simp [repairRun,hc]
    | some a =>
      exact (show TaskState.retired s ⊆ TaskState.retired (retireNode s (R.target a)) by
        rw [retireNode_retired]; exact Finset.subset_union_left).trans
        (by simpa [repairRun,hc] using ih (retireNode s (R.target a)))

theorem repairRun_ready (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) {s : State L M ell} (hs : Ready s) : Ready (repairRun R p n s).1 := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    cases hc : choose R p s with
    | none => simpa [repairRun,hc] using hs
    | some a => simpa [repairRun,hc] using ih (retireSet_ready hs (subtree (R.target a)))

theorem repairRun_terminal (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) (s : State L M ell)
    (hn : (unretired (TaskState.retired s)).card ≤ n) :
    choose R p (repairRun R p n s).1 = none := by
  induction n generalizing s with
  | zero =>
    change choose R p s = none
    cases hc : choose R p s with
    | none => rfl
    | some a =>
      have hp := retirement_progress (TaskState.retired s) (R.target a) (choose_spec R p s hc).2.2
      omega
  | succ n ih =>
    cases hc : choose R p s with
    | none => simp [repairRun,hc]
    | some a =>
      have hp := retirement_progress (TaskState.retired s) (R.target a) (choose_spec R p s hc).2.2
      have hb : (unretired (TaskState.retired (retireNode s (R.target a)))).card ≤ n := by
        rw [retireNode_retired]; omega
      simpa [repairRun,hc] using ih (retireNode s (R.target a)) hb

theorem repairRun_length (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) (s : State L M ell) :
    (repairRun R p n s).2.length ≤ (unretired (TaskState.retired s)).card := by
  induction n generalizing s with
  | zero => simp [repairRun]
  | succ n ih =>
    cases hc : choose R p s with
    | none => simp [repairRun,hc]
    | some a =>
      have hp := retirement_progress (TaskState.retired s) (R.target a) (choose_spec R p s hc).2.2
      have hi := ih (retireNode s (R.target a))
      rw [retireNode_retired] at hi
      simpa only [repairRun,hc,List.length_cons] using (show
        (repairRun R p n (retireNode s (R.target a))).2.length+1 ≤
          (unretired (TaskState.retired s)).card by omega)

def normal (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) : State L M ell :=
  match p.kind with
  | .ordinary => ordinaryStep (R.hit s p.point) s
  | .rich => richComplete s

theorem normal_ready (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (hell : 0 < ell) : Ready (normal R p s) := by
  cases hk : p.kind
  · simpa [normal,hk] using ordinaryStep_ready (R.hit s p.point) hs hell
  · simpa [normal,hk] using richComplete_ready hs

/-- Before and after are distinct snapshots: the next current leaf never
receives another normal operation at this selected point. -/
structure Receipt (L M ell : ℕ) (X Action : Type*) where
  pending : Pending X
  beforeNormal : State L M ell
  afterNormal : State L M ell
  repairs : List (State L M ell × Action)

def serve (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) :
    Receipt L M ell X Action :=
  let out := repairRun R p (8^L) s
  ⟨p,out.1,normal R p out.1,out.2⟩

@[simp] theorem serve_pending (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) :
    (serve R p s).pending = p := rfl

theorem serve_terminal (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) :
    choose R p (serve R p s).beforeNormal = none := by
  apply repairRun_terminal
  exact (Finset.card_le_univ _).trans_eq (leaf_card L)

theorem serve_ready (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (hell : 0 < ell) : Ready (serve R p s).afterNormal :=
  normal_ready R p (repairRun_ready R p _ hs) hell

theorem serve_repairs_length (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) :
    (serve R p s).repairs.length ≤ 8^L :=
  (repairRun_length R p _ s).trans ((Finset.card_le_univ _).trans_eq (leaf_card L))

/-- Internal phases do not ask the policy for a new point. A receipt and a
frozen state are absorbing until an external policy explicitly accepts them. -/
inductive Phase (L M ell : ℕ) (X Action : Type*) where
  | repairing (pending : Pending X) (state : State L M ell)
  | normal (pending : Pending X) (state : State L M ell)
  | delivered (pending : Pending X) (beforeNormal afterNormal : State L M ell)
  | frozen (pending : Pending X) (state : State L M ell)

def tick (R : Rules L M ell X Action) : Phase L M ell X Action → Phase L M ell X Action
  | .repairing p s => match choose R p s with
    | none => .normal p s
    | some a => .repairing p (retireNode s (R.target a))
  | .normal p s => .delivered p s (normal R p s)
  | .delivered p before after => .delivered p before after
  | .frozen p s => .frozen p s

def point : Phase L M ell X Action → X
  | .repairing p _ | .normal p _ | .frozen p _ => p.point
  | .delivered p _ _ => p.point

@[simp] theorem tick_point (R : Rules L M ell X Action) (q : Phase L M ell X Action) :
    point (tick R q) = point q := by
  cases q with
  | repairing p s => cases hc : choose R p s <;> simp [tick,hc,point]
  | normal p s => rfl
  | delivered p before after => rfl
  | frozen p s => rfl

/-- Stopping is checked before the next repair test or reply assembly. In
particular a disclosure reached by an update can freeze before its raw data
is delivered. This operation itself reads no raw target parameter. -/
def freeze (stop : State L M ell → Bool) : Phase L M ell X Action → Phase L M ell X Action
  | .repairing p s => if stop s then .frozen p s else .repairing p s
  | .normal p s => if stop s then .frozen p s else .normal p s
  | .delivered p before after => if stop after then .frozen p after else .delivered p before after
  | .frozen p s => .frozen p s

@[simp] theorem freeze_point (stop : State L M ell → Bool) (q : Phase L M ell X Action) :
    point (freeze stop q) = point q := by
  cases q <;> simp only [freeze] <;> split_ifs <;> rfl

@[simp] theorem tick_frozen (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) :
    tick R (.frozen p s) = .frozen p s := rfl

end GradientHessian.ComparisonController
