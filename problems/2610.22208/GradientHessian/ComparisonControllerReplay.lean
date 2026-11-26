import GradientHessian.VisibilityWindow

/-!
# Suppression, frozen-point replay, and actual visibility lists

Suppressing repair predicates is a definition on the executable rules. The
guarded phase transition freezes before using a state whose prescribed data
have been disclosed. Replay below requires equality only of the remaining
predicates at open states; it does not assume oracle correctness or freshness.
-/

noncomputable section
namespace GradientHessian.ComparisonControllerReplay

open Classical FrontierState TaskState TaskSlots ComparisonController VisibilityWindow

variable {L M ell : ℕ} {X Action : Type*}

def suppress (R : Rules L M ell X Action) (blocked : Action → Bool) : Rules L M ell X Action :=
  { R with trigger := fun s x a => if blocked a then false else R.trigger s x a }

@[simp] theorem suppress_blocked (R : Rules L M ell X Action) (blocked : Action → Bool)
    (s : State L M ell) (x : X) {a : Action} (ha : blocked a=true) :
    (suppress R blocked).trigger s x a=false := by simp [suppress,ha]

@[simp] theorem suppress_unblocked (R : Rules L M ell X Action) (blocked : Action → Bool)
    (s : State L M ell) (x : X) {a : Action} (ha : blocked a=false) :
    (suppress R blocked).trigger s x a=R.trigger s x a := by simp [suppress,ha]

theorem choose_congr (R S : Rules L M ell X Action) (p : Pending X) (s : State L M ell)
    (hp : R.priority=S.priority) (ht : R.target=S.target)
    (hh : ∀ a,R.trigger s p.point a=S.trigger s p.point a) : choose R p s=choose S p s := by
  simp only [ComparisonController.choose,hp,ht]
  congr 1
  funext a
  rw [hh a]

theorem normal_congr (R S : Rules L M ell X Action) (p : Pending X) (s : State L M ell)
    (hh : R.hit s p.point=S.hit s p.point) : normal R p s=normal S p s := by
  cases hk : p.kind <;> simp [normal,hk,hh]

theorem repairRun_congr (R S : Rules L M ell X Action) (p : Pending X) (n : ℕ)
    (s : State L M ell) (hp : R.priority=S.priority) (ht : R.target=S.target)
    (hh : ∀ t a,R.trigger t p.point a=S.trigger t p.point a) :
    repairRun R p n s=repairRun S p n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have he := choose_congr R S p s hp ht (hh s)
    cases hc : choose S p s with
    | none => simp [repairRun,he,hc]
    | some a => simp [repairRun,he,hc,ht,ih]

/-- Both entry and exit guards matter: a retirement can disclose the target,
and this freezes before returning the newly assembled receipt. -/
def guardedTick (R : Rules L M ell X Action) (stop : State L M ell → Bool)
    (q : Phase L M ell X Action) : Phase L M ell X Action :=
  freeze stop (tick R (freeze stop q))

@[simp] theorem guardedTick_point (R : Rules L M ell X Action) (stop : State L M ell → Bool)
    (q : Phase L M ell X Action) : point (guardedTick R stop q)=point q := by
  simp [guardedTick]

@[simp] theorem guardedTick_frozen (R : Rules L M ell X Action) (stop : State L M ell → Bool)
    (p : Pending X) (s : State L M ell) :
    guardedTick R stop (.frozen p s)=.frozen p s := rfl

theorem guardedTick_congr (R S : Rules L M ell X Action) (stop : State L M ell → Bool)
    (hp : R.priority=S.priority) (ht : R.target=S.target)
    (htrigger : ∀ s,stop s=false → ∀ x a,R.trigger s x a=S.trigger s x a)
    (hhit : ∀ s,stop s=false → ∀ x,R.hit s x=S.hit s x)
    (q : Phase L M ell X Action) : guardedTick R stop q=guardedTick S stop q := by
  cases q with
  | frozen p s => rfl
  | delivered p before after => simp [guardedTick,freeze,tick]; split_ifs <;> rfl
  | repairing p s =>
    cases hs : stop s with
    | true => simp [guardedTick,freeze,hs,tick]
    | false =>
      have he := choose_congr R S p s hp ht (htrigger s hs p.point)
      simp only [guardedTick,freeze,hs,Bool.false_eq_true,if_false,tick,he,ht]
  | normal p s =>
    cases hs : stop s with
    | true => simp [guardedTick,freeze,hs,tick]
    | false =>
      have he := normal_congr R S p s (hhit s hs p.point)
      simp only [guardedTick,freeze,hs,Bool.false_eq_true,if_false,tick,he]

def guardedRun (R : Rules L M ell X Action) (stop : State L M ell → Bool) :
    ℕ → Phase L M ell X Action → Phase L M ell X Action
  | 0,q => q
  | n+1,q => guardedRun R stop n (guardedTick R stop q)

theorem guardedRun_congr (R S : Rules L M ell X Action) (stop : State L M ell → Bool)
    (hp : R.priority=S.priority) (ht : R.target=S.target)
    (htrigger : ∀ s,stop s=false → ∀ x a,R.trigger s x a=S.trigger s x a)
    (hhit : ∀ s,stop s=false → ∀ x,R.hit s x=S.hit s x)
    (n : ℕ) (q : Phase L M ell X Action) : guardedRun R stop n q=guardedRun S stop n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [guardedRun,guardedTick_congr R S stop hp ht htrigger hhit,ih]

/-- Changing the blocked predicates has no effect on the guarded process.
The nonblocked predicates and normal decisions must agree before stopping. -/
theorem suppressed_guardedRun_congr (R S : Rules L M ell X Action)
    (blocked : Action → Bool) (stop : State L M ell → Bool)
    (hp : R.priority=S.priority) (ht : R.target=S.target)
    (htrigger : ∀ s,stop s=false → ∀ x a,blocked a=false → R.trigger s x a=S.trigger s x a)
    (hhit : ∀ s,stop s=false → ∀ x,R.hit s x=S.hit s x)
    (n : ℕ) (q : Phase L M ell X Action) :
    guardedRun (suppress R blocked) stop n q=guardedRun (suppress S blocked) stop n q := by
  refine guardedRun_congr (suppress R blocked) (suppress S blocked) stop hp ht ?_ hhit n q
  intro s hs x a
  cases hb : blocked a with
  | true => simp [suppress,hb]
  | false => simpa [suppress,hb] using htrigger s hs x a hb

/-- A future mark stops being hidden on supply, before its first readout. -/
def markSupplied (leaf : Leaf L) (j : Fin M) (s : State L M ell) : Bool :=
  decide (leaf ∈ TaskState.retired s ∨
    TaskState.current s=some leaf ∧ j.val ≤ (s.completed leaf).val)

/-- The corresponding register block is disclosed on this task's completion. -/
def taskDisclosed (leaf : Leaf L) (j : Fin M) (s : State L M ell) : Bool :=
  decide (j.val < (s.completed leaf).val)

def leafDisclosed (leaf : Leaf L) (s : State L M ell) : Bool :=
  decide ((s.completed leaf).val=M)

@[simp] theorem leafDisclosed_iff (leaf : Leaf L) (s : State L M ell) :
    leafDisclosed leaf s=true ↔ leaf ∈ TaskState.retired s := by simp [leafDisclosed]

/-- One point per reply, even if the node becomes visible several times
within its repair trace. The entries are actual selected physical points. -/
def seenPoints (R : Rules L M ell X Action) (v : Node L) :
    List (Pending X) → State L M ell → List X
  | [],_ => []
  | p::ps,s =>
    let tail := seenPoints R v ps (serve R p s).afterNormal
    if Seen R p s v then p.point::tail else tail

theorem seenPoints_length (R : Rules L M ell X Action) (v : Node L)
    (ps : List (Pending X)) (s : State L M ell) :
    (seenPoints R v ps s).length=visibleCount R v ps s := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [seenPoints,visibleCount,seenBit]
    split_ifs <;> simp [ih,Nat.add_comm]

theorem seenPoints_length_le (R : Rules L M ell X Action) (v : Node L)
    (ps : List (Pending X)) {s : State L M ell} (hs : Ready s) (hell : 0 < ell) :
    (seenPoints R v ps s).length ≤ 8^(L-v.1.val)*M*ell := by
  rw [seenPoints_length]
  exact visibility_window_bound R v ps hs hell

theorem mem_seenPoints (R : Rules L M ell X Action) (v : Node L)
    (ps : List (Pending X)) (s : State L M ell) {x : X}
    (hx : x ∈ seenPoints R v ps s) : ∃ p ∈ ps,p.point=x := by
  induction ps generalizing s with
  | nil => simp [seenPoints] at hx
  | cons p ps ih =>
    simp only [seenPoints] at hx
    split_ifs at hx
    · rcases List.mem_cons.mp hx with he | hx
      · exact ⟨p,List.mem_cons_self,he.symm⟩
      · obtain ⟨q,hq,hx⟩ := ih _ hx
        exact ⟨q,List.mem_cons_of_mem _ hq,hx⟩
    · obtain ⟨q,hq,hx⟩ := ih _ hx
      exact ⟨q,List.mem_cons_of_mem _ hq,hx⟩

end GradientHessian.ComparisonControllerReplay
