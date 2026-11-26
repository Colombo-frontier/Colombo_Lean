import GradientHessian.VisibilityTaskWindow

/-! Only the current unretired leaf can have begun a task. In particular,
opening a new current leaf by repair or by a normal operation supplies its
first mark with a zero slot counter. This is a proved reachable invariant. -/

noncomputable section
namespace GradientHessian.ComparisonControllerInvariant

open Classical FrontierState TaskState TaskSlots ComparisonController
open VisibilityWindow VisibilityTaskWindow

variable {L M ell : ℕ} {X Action : Type*}

def Unopened (s : State L M ell) : Prop :=
  ∀ leaf,leaf ∉ TaskState.retired s → TaskState.current s ≠ some leaf →
    s.completed leaf=0 ∧ s.slots leaf=0

theorem initial_unopened : Unopened (initial : State L M ell) := by
  intro leaf _ _
  exact ⟨rfl,rfl⟩

theorem retireSet_unopened {s : State L M ell} (hs : Unopened s) (S : Finset (Leaf L)) :
    Unopened (retireSet s S) := by
  intro leaf hl hc
  have hnot : leaf ∉ TaskState.retired s ∧ leaf ∉ S := by
    simpa only [retired_retireSet,Finset.mem_union,not_or] using hl
  have hcur : TaskState.current s ≠ some leaf := by
    intro he
    exact hc (current_preserved (by rw [retired_retireSet]; exact Finset.subset_union_left) he hl)
  simpa only [retireSet,if_neg hnot.2] using hs leaf hnot.1 hcur

theorem repairRun_unopened (R : Rules L M ell X Action) (p : Pending X) (n : ℕ)
    {s : State L M ell} (hs : Unopened s) : Unopened (repairRun R p n s).1 := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    cases ha : choose R p s with
    | none => simpa [repairRun,ha] using hs
    | some a => simpa [repairRun,ha] using ih (retireSet_unopened hs (subtree (R.target a)))

theorem normal_retired_mono (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) : TaskState.retired s ⊆ TaskState.retired (normal R p s) := by
  intro leaf hl
  have hc := normal_completed_mono R p hs leaf
  have he := (mem_retired _ _).mp hl
  have hb := ((normal R p s).completed leaf).isLt
  apply (mem_retired _ _).mpr
  omega

theorem normal_other (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell)
    {cur leaf : Leaf L} (hc : TaskState.current s=some cur) (hne : leaf ≠ cur) :
    (normal R p s).completed leaf=s.completed leaf ∧ (normal R p s).slots leaf=s.slots leaf := by
  cases hk : p.kind with
  | ordinary => simpa [normal,hk] using ordinaryStep_other (R.hit s p.point) s hc leaf hne
  | rich => simpa [normal,hk] using richComplete_other s hc leaf hne

theorem normal_unopened (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hr : Ready s) (hs : Unopened s) : Unopened (normal R p s) := by
  intro leaf hl hc
  have hm := normal_retired_mono R p hr
  have ho : leaf ∉ TaskState.retired s := fun he => hl (hm he)
  have hn : TaskState.current s ≠ some leaf := by
    intro he
    exact hc (current_preserved hm he hl)
  have hh := hs leaf ho hn
  cases hcur : TaskState.current s with
  | none => cases hk : p.kind <;> simpa [normal,hk,ordinaryStep,richComplete,hcur] using hh
  | some cur =>
    have hne : leaf ≠ cur := by intro he; subst leaf; exact hn hcur
    simpa only [(normal_other R p s hcur hne).1,(normal_other R p s hcur hne).2] using hh

theorem serve_unopened (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hr : Ready s) (hs : Unopened s) : Unopened (serve R p s).afterNormal :=
  normal_unopened R p (repairRun_ready R p _ hr) (repairRun_unopened R p _ hs)

theorem run_unopened (R : Rules L M ell X Action) (ps : List (Pending X))
    {s : State L M ell} (hr : Ready s) (hs : Unopened s) (hell : 0 < ell) :
    Unopened (run R ps s) := by
  induction ps generalizing s with
  | nil => exact hs
  | cons p ps ih => exact ih (serve_ready R p hr hell) (serve_unopened R p hr hs)

theorem repairRun_live_unchanged (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) (s : State L M ell) (leaf : Leaf L)
    (hl : leaf ∉ TaskState.retired (repairRun R p n s).1) :
    (repairRun R p n s).1.completed leaf=s.completed leaf ∧
      (repairRun R p n s).1.slots leaf=s.slots leaf := by
  induction n generalizing s with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    cases ha : choose R p s with
    | none => simp [repairRun,ha]
    | some a =>
      have hlast : leaf ∉ TaskState.retired (repairRun R p n (retireNode s (R.target a))).1 := by
        simpa [repairRun,ha] using hl
      have hmid : leaf ∉ TaskState.retired (retireNode s (R.target a)) :=
        fun he => hlast (repairRun_retired_mono R p n _ he)
      have hout : leaf ∉ subtree (R.target a) := by
        rw [retireNode_retired] at hmid
        exact fun he => hmid (Finset.mem_union_right _ he)
      simpa only [repairRun,ha,retireNode,retireSet,if_neg hout] using ih _ hlast

theorem repair_new_current_zero (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) {s : State L M ell} (hs : Unopened s) {leaf : Leaf L}
    (hold : TaskState.current s ≠ some leaf)
    (hnew : TaskState.current (repairRun R p n s).1=some leaf) :
    (repairRun R p n s).1.completed leaf=0 ∧ (repairRun R p n s).1.slots leaf=0 := by
  have hn := ((FrontierState.current_eq_some_iff _ _).mp hnew).1
  have ho : leaf ∉ TaskState.retired s := fun he => hn (repairRun_retired_mono R p n s he)
  have hh := hs leaf ho hold
  simpa only [(repairRun_live_unchanged R p n s leaf hn).1,
    (repairRun_live_unchanged R p n s leaf hn).2] using hh

theorem normal_new_current_zero (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hr : Ready s) (hs : Unopened s) {leaf : Leaf L}
    (hold : TaskState.current s ≠ some leaf) (hnew : TaskState.current (normal R p s)=some leaf) :
    (normal R p s).completed leaf=0 ∧ (normal R p s).slots leaf=0 := by
  have hn := ((FrontierState.current_eq_some_iff _ _).mp hnew).1
  have ho : leaf ∉ TaskState.retired s := fun he => hn (normal_retired_mono R p hr he)
  have hh := hs leaf ho hold
  cases hc : TaskState.current s with
  | none => cases hk : p.kind <;> simpa [normal,hk,ordinaryStep,richComplete,hc] using hh
  | some cur =>
    have hne : leaf ≠ cur := by intro he; subst leaf; exact hold hc
    simpa only [(normal_other R p s hc hne).1,(normal_other R p s hc hne).2] using hh

end GradientHessian.ComparisonControllerInvariant
