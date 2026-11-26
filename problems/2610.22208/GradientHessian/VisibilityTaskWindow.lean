import GradientHessian.VisibilityWindow

/-! The number of ordinary products actually assigned to any fixed marked
task is at most ell. Repair and rich retirement cannot restart that task. -/

noncomputable section
namespace GradientHessian.VisibilityTaskWindow

open Classical FrontierState TaskState TaskSlots ComparisonController VisibilityWindow

variable {L M ell : ℕ} {X Action : Type*}

def taskCredit (s : State L M ell) (leaf : Leaf L) (j : Fin M) : ℕ :=
  if j.val < (s.completed leaf).val then ell
  else if j.val = (s.completed leaf).val then (s.slots leaf).val else 0

theorem taskCredit_le (s : State L M ell) (leaf : Leaf L) (j : Fin M) :
    taskCredit s leaf j ≤ ell := by
  have := (s.slots leaf).isLt
  unfold taskCredit
  split_ifs <;> omega

theorem taskCredit_mono {s t : State L M ell} (leaf : Leaf L) (j : Fin M)
    (hc : (s.completed leaf).val ≤ (t.completed leaf).val)
    (hw : work s leaf ≤ work t leaf) : taskCredit s leaf j ≤ taskCredit t leaf j := by
  by_cases he : (s.completed leaf).val = (t.completed leaf).val
  · have hslot : (s.slots leaf).val ≤ (t.slots leaf).val := by
      simp only [work,he] at hw
      omega
    simp only [taskCredit,he]
    split_ifs <;> omega
  · have hlt : (s.completed leaf).val < (t.completed leaf).val := by omega
    have hs := taskCredit_le s leaf j
    by_cases hj : j.val < (t.completed leaf).val
    · simpa [taskCredit,hj] using hs
    · have h₁ : ¬j.val < (s.completed leaf).val := by omega
      have h₂ : ¬j.val = (s.completed leaf).val := by omega
      simp [taskCredit,h₁,h₂]

theorem retireSet_completed_mono (s : State L M ell) (S : Finset (Leaf L)) (leaf : Leaf L) :
    (s.completed leaf).val ≤ ((retireSet s S).completed leaf).val := by
  by_cases hl : leaf ∈ S
  · have := (s.completed leaf).isLt
    simp only [retireSet,if_pos hl,Fin.val_last]
    omega
  · simp [retireSet,hl]

theorem repairRun_completed_mono (R : Rules L M ell X Action) (p : Pending X)
    (n : ℕ) (s : State L M ell) (leaf : Leaf L) :
    (s.completed leaf).val ≤ ((repairRun R p n s).1.completed leaf).val := by
  induction n generalizing s with
  | zero => exact le_rfl
  | succ n ih =>
    cases ha : choose R p s with
    | none => simp [repairRun,ha]
    | some a =>
      exact (retireSet_completed_mono s (subtree (R.target a)) leaf).trans
        (by simpa [repairRun,ha] using ih (retireNode s (R.target a)))

theorem normal_completed_mono (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (leaf : Leaf L) :
    (s.completed leaf).val ≤ ((normal R p s).completed leaf).val := by
  cases hc : TaskState.current s with
  | none => cases hk : p.kind <;> simp [normal,hk,ordinaryStep,richComplete,hc]
  | some cur =>
    cases hk : p.kind with
    | rich => simpa [normal,hk,richComplete,hc] using retireSet_completed_mono s {cur} leaf
    | ordinary =>
      simp only [normal,hk]
      by_cases he : leaf=cur
      · subst leaf
        rw [ordinaryStep_eq _ s hc (hs.2 cur (current_live s hc))]
        have hl : ((advanceSlot s cur).completed cur).val < M := by simpa using current_live s hc
        split_ifs
        · rw [completeLeaf_completed _ _ hl,advanceSlot_completed]
          omega
        · simp
      · rw [(ordinaryStep_other _ s hc leaf he).1]

theorem serve_completed_mono (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (leaf : Leaf L) :
    (s.completed leaf).val ≤ ((serve R p s).afterNormal.completed leaf).val :=
  (repairRun_completed_mono R p _ s leaf).trans
    (normal_completed_mono R p (repairRun_ready R p _ hs) leaf)

theorem serve_retired_mono (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) : TaskState.retired s ⊆ TaskState.retired (serve R p s).afterNormal := by
  intro leaf hl
  have hc := serve_completed_mono R p hs leaf
  have he := (mem_retired _ _).mp hl
  have hb := ((serve R p s).afterNormal.completed leaf).isLt
  apply (mem_retired _ _).mpr
  omega

theorem serve_taskCredit_mono (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (leaf : Leaf L) (j : Fin M) :
    taskCredit s leaf j ≤ taskCredit (serve R p s).afterNormal leaf j :=
  taskCredit_mono leaf j (serve_completed_mono R p hs leaf) (serve_work_mono R p hs leaf)

theorem normal_current_task_progress (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) {leaf : Leaf L} (j : Fin M)
    (hc : TaskState.current s = some leaf) (hj : (s.completed leaf).val=j.val) :
    taskCredit s leaf j < taskCredit (normal R p s) leaf j := by
  have hslot := hs.2 leaf (current_live s hc)
  have hjlt : j.val < M := j.isLt
  have hstart : taskCredit s leaf j=(s.slots leaf).val := by simp [taskCredit,hj]
  rw [hstart]
  cases hk : p.kind with
  | rich => simpa [normal,hk,richComplete,hc,taskCredit,retireSet,hjlt] using hslot
  | ordinary =>
    simp only [normal,hk]
    rw [ordinaryStep_eq _ s hc hslot]
    have hl : ((advanceSlot s leaf).completed leaf).val < M := by simpa using current_live s hc
    split_ifs
    · simp only [taskCredit,completeLeaf_completed _ _ hl,advanceSlot_completed,hj]
      simp only [Nat.lt_add_one,if_true]
      exact hslot
    · simp only [taskCredit,advanceSlot_completed,hj,lt_self_iff_false,if_false,if_true]
      rw [advanceSlot_slots s leaf (current_live s hc) hslot]
      omega

/-- Counted exactly when the unique normal operation uses this leaf's matrix
while this mark is current. Ordinary points swallowed by repairs do not count. -/
def Consumes (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell)
    (leaf : Leaf L) (j : Fin M) : Prop :=
  p.kind=.ordinary ∧ TaskState.current (serve R p s).beforeNormal=some leaf ∧
    ((serve R p s).beforeNormal.completed leaf).val=j.val

def consumeBit (R : Rules L M ell X Action) (p : Pending X) (s : State L M ell)
    (leaf : Leaf L) (j : Fin M) : ℕ := if Consumes R p s leaf j then 1 else 0

theorem consumeBit_credit (R : Rules L M ell X Action) (p : Pending X)
    {s : State L M ell} (hs : Ready s) (leaf : Leaf L) (j : Fin M) :
    consumeBit R p s leaf j+taskCredit s leaf j ≤ taskCredit (serve R p s).afterNormal leaf j := by
  by_cases hh : Consumes R p s leaf j
  · have hpre := taskCredit_mono leaf j (repairRun_completed_mono R p (8^L) s leaf)
      (repairRun_work_mono R p (8^L) hs leaf)
    have hstep := normal_current_task_progress R p (repairRun_ready R p (8^L) hs) j hh.2.1 hh.2.2
    simp only [consumeBit,if_pos hh]
    change 1+taskCredit s leaf j ≤ taskCredit (normal R p (repairRun R p (8^L) s).1) leaf j
    omega
  · simp only [consumeBit,if_neg hh,Nat.zero_add]
    exact serve_taskCredit_mono R p hs leaf j

def consumedSlots (R : Rules L M ell X Action) (leaf : Leaf L) (j : Fin M) :
    List (Pending X) → State L M ell → ℕ
  | [],_ => 0
  | p::ps,s => consumeBit R p s leaf j+consumedSlots R leaf j ps (serve R p s).afterNormal

theorem consumedSlots_credit (R : Rules L M ell X Action) (leaf : Leaf L) (j : Fin M)
    (ps : List (Pending X)) {s : State L M ell} (hs : Ready s) (hell : 0 < ell) :
    consumedSlots R leaf j ps s+taskCredit s leaf j ≤ taskCredit (run R ps s) leaf j := by
  induction ps generalizing s with
  | nil => simp [consumedSlots,run]
  | cons p ps ih =>
    have hi := ih (serve_ready R p hs hell)
    have hp := consumeBit_credit R p hs leaf j
    simp only [consumedSlots,run]
    omega

theorem marked_task_slot_bound (R : Rules L M ell X Action) (leaf : Leaf L) (j : Fin M)
    (ps : List (Pending X)) {s : State L M ell} (hs : Ready s) (hell : 0 < ell) :
    consumedSlots R leaf j ps s ≤ ell := by
  have hc := consumedSlots_credit R leaf j ps hs hell
  have hb := taskCredit_le (run R ps s) leaf j
  omega

end GradientHessian.VisibilityTaskWindow
