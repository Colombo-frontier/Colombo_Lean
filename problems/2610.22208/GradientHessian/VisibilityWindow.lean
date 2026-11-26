import GradientHessian.ComparisonController

/-!
# Deterministic visibility windows of the comparison controller

Visibility includes every intermediate repair state at the frozen selected
point. A visible current leaf either retires during repairs, or remains
current for the unique normal operation. Its finite work strictly increases.
Consequently a subtree is seen at at most its number of tasks times ell
selected points. No visibility bound is a hypothesis of these theorems.
-/

noncomputable section
namespace GradientHessian.VisibilityWindow

open Classical FrontierState TaskState TaskSlots ComparisonController
open scoped BigOperators

variable {L M ell : ℕ} {X Action : Type*}

theorem normal_work_mono (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (leaf : Leaf L) :
    work s leaf ≤ work (normal R p s) leaf := by
  cases hc : TaskState.current s with
  | none => cases hk : p.kind <;> simp [normal,hk,ordinaryStep,richComplete,hc]
  | some cur =>
    cases hk : p.kind with
    | ordinary =>
      simp only [normal,hk]
      by_cases he : leaf=cur
      · subst leaf
        exact (ordinaryStep_work_progress _ s hc (hs.2 cur (current_live s hc))).le
      · have hh := ordinaryStep_other (R.hit s p.point) s hc leaf he
        simp [work,hh.1,hh.2]
    | rich => simpa [normal,hk,richComplete,hc] using retireSet_work_mono hs.1 {cur} leaf

theorem normal_current_progress (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) {leaf : Leaf L}
    (hc : TaskState.current s = some leaf) : work s leaf < work (normal R p s) leaf := by
  cases hk : p.kind with
  | ordinary => simpa [normal,hk] using
      ordinaryStep_work_progress (R.hit s p.point) s hc (hs.2 leaf (current_live s hc))
  | rich => simpa [normal,hk,richComplete,hc] using
      retireSet_work_progress hs {leaf} (Finset.mem_singleton_self leaf) (current_live s hc)

theorem repairRun_work_mono (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) {s : State L M ell} (hs : Ready s) (leaf : Leaf L) :
    work s leaf ≤ work (repairRun R p n s).1 leaf := by
  induction n generalizing s with
  | zero => exact le_rfl
  | succ n ih =>
    cases hc : choose R p s with
    | none => simp [repairRun,hc]
    | some a =>
      exact (retireSet_work_mono hs.1 (subtree (R.target a)) leaf).trans
        (by simpa [repairRun,hc] using ih (retireSet_ready hs (subtree (R.target a))))

theorem current_preserved {s t : State L M ell}
    (hst : TaskState.retired s ⊆ TaskState.retired t) {leaf : Leaf L}
    (hc : TaskState.current s = some leaf) (hl : leaf ∉ TaskState.retired t) :
    TaskState.current t = some leaf := by
  apply (FrontierState.current_eq_some_iff _ _).mpr
  exact ⟨hl,fun other ho => ((FrontierState.current_eq_some_iff _ _).mp hc).2 other
    (fun hm => ho (hst hm))⟩

theorem work_lt_capacity {s : State L M ell} (hs : Ready s) {leaf : Leaf L}
    (hl : (s.completed leaf).val < M) : work s leaf < M*ell := by
  have hslot := hs.2 leaf hl
  have hmul := Nat.mul_le_mul_right ell (show (s.completed leaf).val+1 ≤ M by omega)
  unfold work
  nlinarith

/-- A leaf current at the start cannot be skipped by repairs while it remains
unretired. It therefore makes progress before this reply completes. -/
theorem repaired_current_progress (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) {s : State L M ell} (hs : Ready s) {leaf : Leaf L}
    (hc : TaskState.current s = some leaf) :
    work s leaf < work (normal R p (repairRun R p n s).1) leaf := by
  have ht := repairRun_ready R p n hs
  by_cases hl : leaf ∈ TaskState.retired (repairRun R p n s).1
  · have he := (mem_retired _ _).mp hl
    have hz := ht.1 leaf he
    have hw : work (repairRun R p n s).1 leaf=M*ell := by simp [work,he,hz]
    exact (work_lt_capacity hs (current_live s hc)).trans_le
      (by rw [← hw]; exact normal_work_mono R p ht leaf)
  · exact (repairRun_work_mono R p n hs leaf).trans_lt
      (normal_current_progress R p ht (current_preserved (repairRun_retired_mono R p n s) hc hl))

/-- This also covers nodes first exposed in the middle of the repair loop. -/
theorem visits_current_progress (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) {s u : State L M ell} (hs : Ready s)
    (hu : u ∈ visits R p n s) {leaf : Leaf L} (hc : TaskState.current u = some leaf) :
    work s leaf < work (normal R p (repairRun R p n s).1) leaf := by
  induction n generalizing s with
  | zero =>
    have he : u=s := by simpa [visits,repairRun] using hu
    subst u
    exact normal_current_progress R p hs hc
  | succ n ih =>
    cases ha : choose R p s with
    | none =>
      have he : u=s := by simpa [visits,repairRun,ha] using hu
      subst u
      simpa [repairRun,ha] using normal_current_progress R p hs hc
    | some a =>
      have hv : u=s ∨ u ∈ visits R p n (retireNode s (R.target a)) := by
        simpa [visits,repairRun,ha] using hu
      rcases hv with rfl | hv
      · exact repaired_current_progress R p (n+1) hs hc
      · have hi := ih (retireSet_ready hs (subtree (R.target a))) hv
        exact (retireSet_work_mono hs.1 (subtree (R.target a)) leaf).trans_lt
          (by simpa [repairRun,ha] using hi)

def Seen (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) (v : Node L) : Prop :=
  ∃ u ∈ visits R p (8^L) s, Visible (TaskState.retired u) v

def subtreeWork (s : State L M ell) (v : Node L) : ℕ := ∑ leaf ∈ subtree v,work s leaf

theorem subtreeWork_le {s : State L M ell} (hs : Ready s) (v : Node L) :
    subtreeWork s v ≤ 8^(L-v.1.val)*M*ell := by
  calc
    _ ≤ ∑ _leaf ∈ subtree v,M*ell := Finset.sum_le_sum (fun leaf _ => work_le hs.1 leaf)
    _ = 8^(L-v.1.val)*M*ell := by simp [subtree_card,Nat.mul_assoc]

theorem serve_work_mono (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (leaf : Leaf L) :
    work s leaf ≤ work (serve R p s).afterNormal leaf :=
  (repairRun_work_mono R p _ hs leaf).trans
    (normal_work_mono R p (repairRun_ready R p _ hs) leaf)

theorem seen_subtreeWork_progress (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (v : Node L) (hv : Seen R p s v) :
    subtreeWork s v < subtreeWork (serve R p s).afterNormal v := by
  obtain ⟨u,hu,leaf,hc,hl⟩ := hv
  apply Finset.sum_lt_sum (fun other _ => serve_work_mono R p hs other)
  exact ⟨leaf,(mem_subtree _ _).mpr hl,visits_current_progress R p _ hs hu hc⟩

def seenBit (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell) (v : Node L) : ℕ :=
  if Seen R p s v then 1 else 0

theorem seenBit_credit (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (v : Node L) :
    seenBit R p s v+subtreeWork s v ≤ subtreeWork (serve R p s).afterNormal v := by
  by_cases hv : Seen R p s v
  · have hh := seen_subtreeWork_progress R p hs v hv
    simp only [seenBit,if_pos hv]
    omega
  · simp only [seenBit,if_neg hv,Nat.zero_add,subtreeWork]
    exact Finset.sum_le_sum (fun leaf _ => serve_work_mono R p hs leaf)

def run (R : Rules L M ell X Action) : List (Pending X) → State L M ell → State L M ell
  | [],s => s
  | p::ps,s => run R ps (serve R p s).afterNormal

def visibleCount (R : Rules L M ell X Action) (v : Node L) :
    List (Pending X) → State L M ell → ℕ
  | [],_ => 0
  | p::ps,s => seenBit R p s v+visibleCount R v ps (serve R p s).afterNormal

theorem run_ready (R : Rules L M ell X Action) (ps : List (Pending X))
    {s : State L M ell} (hs : Ready s) (hell : 0 < ell) : Ready (run R ps s) := by
  induction ps generalizing s with
  | nil => exact hs
  | cons p ps ih => exact ih (serve_ready R p hs hell)

theorem visibleCount_credit (R : Rules L M ell X Action) (v : Node L) (ps : List (Pending X))
    {s : State L M ell} (hs : Ready s) (hell : 0 < ell) :
    visibleCount R v ps s+subtreeWork s v ≤ subtreeWork (run R ps s) v := by
  induction ps generalizing s with
  | nil => simp [visibleCount,run]
  | cons p ps ih =>
    have hi := ih (serve_ready R p hs hell)
    have hp := seenBit_credit R p hs v
    simp only [visibleCount,run]
    omega

/-- Uniform over all geometric tests, including any suppressed-test variant,
and over every finite selected-point history, including a virtual output. -/
theorem visibility_window_bound (R : Rules L M ell X Action) (v : Node L)
    (ps : List (Pending X)) {s : State L M ell} (hs : Ready s) (hell : 0 < ell) :
    visibleCount R v ps s ≤ 8^(L-v.1.val)*M*ell := by
  have hc := visibleCount_credit R v ps hs hell
  have hb := subtreeWork_le (run_ready R ps hs hell) v
  omega

theorem leaf_visibility_window_bound (R : Rules L M ell X Action) (leaf : Leaf L)
    (ps : List (Pending X)) {s : State L M ell} (hs : Ready s) (hell : 0 < ell) :
    visibleCount R (leafNode leaf) ps s ≤ M*ell := by
  simpa [leafNode] using visibility_window_bound R (leafNode leaf) ps hs hell

end GradientHessian.VisibilityWindow
