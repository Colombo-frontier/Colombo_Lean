import GradientHessian.TaskState

/-! One ordinary slot, the literal timeout decision, and a strictly increasing
finite task-work counter. A hit is a Boolean input to this deterministic update;
no bound on that Boolean event is assumed here. -/

noncomputable section
namespace GradientHessian.TaskSlots

open TaskState FrontierState Classical

variable {L M ell : ℕ}

def advanceSlot (s : State L M ell) (leaf : Leaf L) : State L M ell :=
  if hc : (s.completed leaf).val < M then
    if hs : (s.slots leaf).val < ell then
      ⟨s.completed,Function.update s.slots leaf ⟨(s.slots leaf).val+1,by omega⟩⟩
    else s
  else s

@[simp] theorem advanceSlot_completed (s : State L M ell) (leaf : Leaf L) :
    (advanceSlot s leaf).completed = s.completed := by
  unfold advanceSlot
  split_ifs <;> rfl

theorem advanceSlot_slots (s : State L M ell) (leaf : Leaf L)
    (hc : (s.completed leaf).val < M) (hs : (s.slots leaf).val < ell) :
    ((advanceSlot s leaf).slots leaf).val = (s.slots leaf).val+1 := by
  simp [advanceSlot,hc,hs]

theorem advanceSlot_other (s : State L M ell) (leaf other : Leaf L) (hne : other ≠ leaf) :
    (advanceSlot s leaf).slots other = s.slots other := by
  unfold advanceSlot
  split_ifs <;> simp [hne]

@[simp] theorem advanceSlot_retired (s : State L M ell) (leaf : Leaf L) :
    TaskState.retired (advanceSlot s leaf) = TaskState.retired s := by
  ext other
  simp

theorem advanceSlot_wellFormed {s : State L M ell} (h : WellFormed s) (leaf : Leaf L) :
    WellFormed (advanceSlot s leaf) := by
  intro other hc
  have he : (s.completed other).val=M := by simpa using hc
  by_cases ho : other=leaf
  · subst other
    have hh : ¬(s.completed leaf).val < M := by omega
    simpa [advanceSlot,hh] using h leaf he
  · simpa only [advanceSlot_other s leaf other ho] using h other he

def ordinaryStep (hit : Bool) (s : State L M ell) : State L M ell :=
  match TaskState.current s with
  | none => s
  | some leaf =>
      let next := advanceSlot s leaf
      if hit || decide ((next.slots leaf).val = ell) then completeLeaf next leaf else next

theorem ordinaryStep_eq (hit : Bool) (s : State L M ell) {leaf : Leaf L}
    (hc : TaskState.current s = some leaf) (hs : (s.slots leaf).val < ell) :
    ordinaryStep hit s =
      if hit=true ∨ (s.slots leaf).val+1=ell then completeLeaf (advanceSlot s leaf) leaf
      else advanceSlot s leaf := by
  simp only [ordinaryStep,hc,Bool.or_eq_true,decide_eq_true_eq,
    advanceSlot_slots s leaf (current_live s hc) hs]

theorem ordinaryStep_other (hit : Bool) (s : State L M ell) {leaf : Leaf L}
    (hc : TaskState.current s = some leaf) (other : Leaf L) (hne : other ≠ leaf) :
    (ordinaryStep hit s).completed other = s.completed other ∧
      (ordinaryStep hit s).slots other = s.slots other := by
  simp only [ordinaryStep,hc]
  split_ifs
  · simpa only [advanceSlot_completed,advanceSlot_other s leaf other hne] using
      completeLeaf_other (advanceSlot s leaf) leaf other hne
  · exact ⟨by simp,advanceSlot_other s leaf other hne⟩

theorem ordinaryStep_completedTotal (hit : Bool) (s : State L M ell) {leaf : Leaf L}
    (hc : TaskState.current s = some leaf) (hs : (s.slots leaf).val < ell) :
    completedTotal (ordinaryStep hit s) = completedTotal s +
      if hit=true ∨ (s.slots leaf).val+1=ell then 1 else 0 := by
  rw [ordinaryStep_eq hit s hc hs]
  have hl : ((advanceSlot s leaf).completed leaf).val < M := by simpa using current_live s hc
  split_ifs with ht
  · rw [completedTotal_completeLeaf _ _ hl]
    simp only [completedTotal,advanceSlot_completed]
  · simp only [completedTotal,advanceSlot_completed,Nat.add_zero]

theorem ordinaryStep_slots (hit : Bool) (s : State L M ell) {leaf : Leaf L}
    (hc : TaskState.current s = some leaf) (hs : (s.slots leaf).val < ell) :
    ((ordinaryStep hit s).slots leaf).val =
      if hit=true ∨ (s.slots leaf).val+1=ell then 0 else (s.slots leaf).val+1 := by
  rw [ordinaryStep_eq hit s hc hs]
  have hl : ((advanceSlot s leaf).completed leaf).val < M := by simpa using current_live s hc
  split_ifs
  · rw [completeLeaf_slots _ _ hl]
    rfl
  · exact advanceSlot_slots s leaf (current_live s hc) hs

theorem ordinaryStep_wellFormed (hit : Bool) {s : State L M ell} (h : WellFormed s) :
    WellFormed (ordinaryStep hit s) := by
  cases hc : TaskState.current s with
  | none => simpa only [ordinaryStep,hc] using h
  | some leaf =>
      simp only [ordinaryStep,hc]
      split_ifs
      · exact completeLeaf_wellFormed (advanceSlot_wellFormed h leaf) leaf
      · exact advanceSlot_wellFormed h leaf

/-- This pre-reply invariant is restored after an ordinary timeout. -/
def Ready (s : State L M ell) : Prop :=
  WellFormed s ∧ ∀ leaf,(s.completed leaf).val < M → (s.slots leaf).val < ell

theorem initial_ready (hell : 0 < ell) : Ready (initial : State L M ell) :=
  ⟨initial_wellFormed,fun _ _ => hell⟩

theorem ordinaryStep_ready (hit : Bool) {s : State L M ell} (h : Ready s) (hell : 0 < ell) :
    Ready (ordinaryStep hit s) := by
  refine ⟨ordinaryStep_wellFormed hit h.1,?_⟩
  intro other hother
  cases hc : TaskState.current s with
  | none => simpa [ordinaryStep,hc] using h.2 other (by simpa [ordinaryStep,hc] using hother)
  | some leaf =>
      by_cases ho : other=leaf
      · subst other
        have hs := h.2 leaf (current_live s hc)
        rw [ordinaryStep_slots hit s hc hs]
        split_ifs with ht
        · exact hell
        · have hn : (s.slots leaf).val+1 ≠ ell := fun he => ht (Or.inr he)
          omega
      · rw [(ordinaryStep_other hit s hc other ho).2]
        exact h.2 other (by simpa only [(ordinaryStep_other hit s hc other ho).1] using hother)

/-- Monotone finite work credit. Each timeout contributes exactly ell;
an early retirement can only discard unused slots and increase the credit. -/
def work (s : State L M ell) (leaf : Leaf L) : ℕ :=
  (s.completed leaf).val*ell+(s.slots leaf).val

theorem work_le {s : State L M ell} (h : WellFormed s) (leaf : Leaf L) : work s leaf ≤ M*ell := by
  have hc := (s.completed leaf).isLt
  have hs := (s.slots leaf).isLt
  by_cases he : (s.completed leaf).val=M
  · simp [work,he,h leaf he]
  · have hm : (s.completed leaf).val+1 ≤ M := by omega
    have hh := Nat.mul_le_mul_right ell hm
    unfold work
    nlinarith

theorem ordinaryStep_work_progress (hit : Bool) (s : State L M ell) {leaf : Leaf L}
    (hc : TaskState.current s = some leaf) (hs : (s.slots leaf).val < ell) :
    work s leaf < work (ordinaryStep hit s) leaf := by
  rw [ordinaryStep_eq hit s hc hs]
  have hl : ((advanceSlot s leaf).completed leaf).val < M := by simpa using current_live s hc
  split_ifs
  · simp only [work]
    rw [completeLeaf_completed _ _ hl,completeLeaf_slots _ _ hl]
    simp only [advanceSlot_completed,Fin.val_zero,Nat.add_zero]
    nlinarith
  · simp only [work]
    rw [advanceSlot_completed,advanceSlot_slots s leaf (current_live s hc) hs]
    omega

theorem retireSet_ready {s : State L M ell} (h : Ready s) (S : Finset (Leaf L)) :
    Ready (retireSet s S) := by
  refine ⟨retireSet_wellFormed h.1 S,?_⟩
  intro leaf hl
  by_cases hs : leaf ∈ S
  · simp [retireSet,hs] at hl
  · simpa [retireSet,hs] using h.2 leaf (by simpa [retireSet,hs] using hl)

theorem normalComplete_ready {s : State L M ell} (h : Ready s) (hell : 0 < ell) :
    Ready (normalComplete s) := by
  refine ⟨normalComplete_wellFormed h.1,?_⟩
  intro other ho
  cases hc : TaskState.current s with
  | none => simpa [normalComplete,hc] using h.2 other (by simpa [normalComplete,hc] using ho)
  | some leaf =>
      by_cases he : other=leaf
      · subst other
        rw [normalComplete_resets_slot s hc]
        exact hell
      · have hh := completeLeaf_other s leaf other he
        simpa only [normalComplete,hc,hh.2] using h.2 other
          (by simpa only [normalComplete,hc,hh.1] using ho)

theorem richComplete_ready {s : State L M ell} (h : Ready s) : Ready (richComplete s) := by
  cases hc : TaskState.current s with
  | none => simpa [richComplete,hc] using h
  | some leaf => simpa [richComplete,hc] using retireSet_ready h {leaf}

theorem retireSet_work_of_mem (s : State L M ell) (S : Finset (Leaf L)) {leaf : Leaf L}
    (hl : leaf ∈ S) : work (retireSet s S) leaf = M*ell := by simp [work,retireSet,hl]

theorem retireSet_work_mono {s : State L M ell} (h : WellFormed s)
    (S : Finset (Leaf L)) (leaf : Leaf L) : work s leaf ≤ work (retireSet s S) leaf := by
  by_cases hl : leaf ∈ S
  · rw [retireSet_work_of_mem s S hl]
    exact work_le h leaf
  · simp [work,retireSet,hl]

theorem retireSet_work_progress {s : State L M ell} (h : Ready s)
    (S : Finset (Leaf L)) {leaf : Leaf L} (hl : leaf ∈ S)
    (hlive : (s.completed leaf).val < M) : work s leaf < work (retireSet s S) leaf := by
  rw [retireSet_work_of_mem s S hl]
  have hslot := h.2 leaf hlive
  have hmul := Nat.mul_le_mul_right ell (show (s.completed leaf).val+1 ≤ M by omega)
  unfold work
  nlinarith

end GradientHessian.TaskSlots
