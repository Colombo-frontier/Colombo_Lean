import GradientHessian.ComparisonController

/-! Disclosure is derived from the actual retirement and task-prefix state.
Every completed subtree reveals all its leaf data and completion blocks;
directions of a task block are disclosed together, never register by register. -/

noncomputable section
namespace GradientHessian.GeometricDisclosure
open Classical FrontierState TaskState

variable {L M ell : ℕ}

def NodeDisclosed (s : State L M ell) (v : Node L) : Prop :=
  subtree v ⊆ TaskState.retired s

def CompletionDisclosed (s : State L M ell) (v : Node L) (hv : v.1.val<L) (i : Fin 8) : Prop :=
  NodeDisclosed s (child v hv i)

def TaskDisclosed (s : State L M ell) (leaf : Leaf L) (j : Fin M) : Prop :=
  j.val < (s.completed leaf).val

def MarkSupplied (s : State L M ell) (leaf : Leaf L) (j : Fin M) : Prop :=
  TaskDisclosed s leaf j ∨ TaskState.current s = some leaf ∧ j.val=(s.completed leaf).val

def LastChildClosed (R : Retired L) : Prop :=
  ∀ (v : Node L) (hv : v.1.val<L), subtree (child v hv (Fin.last 7)) ⊆ R → subtree v ⊆ R

theorem nodeDisclosed_iff_children (s : State L M ell) (v : Node L) (hv : v.1.val<L) :
    NodeDisclosed s v ↔ ∀ i, CompletionDisclosed s v hv i := by
  constructor
  · intro h i
    exact (subtree_child_subset v hv i).trans h
  · intro h leaf hl
    rw [subtree_eq_children v hv] at hl
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hl
    exact h i hi

theorem nodeDisclosed_child {s : State L M ell} {v : Node L} (h : NodeDisclosed s v)
    (hv : v.1.val<L) (i : Fin 8) : CompletionDisclosed s v hv i :=
  (nodeDisclosed_iff_children s v hv).mp h i

@[simp] theorem leafNode_disclosed (s : State L M ell) (leaf : Leaf L) :
    NodeDisclosed s (leafNode leaf) ↔ leaf ∈ TaskState.retired s := by
  simp [NodeDisclosed]

theorem retired_all_tasks_disclosed {s : State L M ell} {leaf : Leaf L}
    (hl : leaf ∈ TaskState.retired s) (j : Fin M) : TaskDisclosed s leaf j := by
  unfold TaskDisclosed
  rw [(TaskState.mem_retired s leaf).mp hl]
  exact j.isLt

theorem nodeDisclosed_all_leaf_data {s : State L M ell} {v : Node L}
    (hv : NodeDisclosed s v) {leaf : Leaf L} (hl : leaf ∈ subtree v) :
    leaf ∈ TaskState.retired s ∧ ∀ j : Fin M, TaskDisclosed s leaf j :=
  ⟨hv hl, retired_all_tasks_disclosed (hv hl)⟩

theorem nodeDisclosed_mono {s s' : State L M ell}
    (h : TaskState.retired s ⊆ TaskState.retired s') {v : Node L}
    (hv : NodeDisclosed s v) : NodeDisclosed s' v := hv.trans h

theorem taskDisclosed_mono {s s' : State L M ell}
    (h : ∀ leaf, (s.completed leaf).val ≤ (s'.completed leaf).val)
    {leaf : Leaf L} {j : Fin M} (hj : TaskDisclosed s leaf j) : TaskDisclosed s' leaf j :=
  hj.trans_le (h leaf)

theorem retireNode_discloses (s : State L M ell) (v : Node L) :
    NodeDisclosed (retireNode s v) v := by
  rw [NodeDisclosed, retireNode_retired]
  exact Finset.subset_union_right

theorem retireNode_discloses_child (s : State L M ell) (v : Node L)
    (hv : v.1.val<L) (i : Fin 8) : CompletionDisclosed (retireNode s v) v hv i :=
  nodeDisclosed_child (retireNode_discloses s v) hv i

theorem current_mark_supplied (s : State L M ell) {leaf : Leaf L}
    (hc : TaskState.current s = some leaf) :
    MarkSupplied s leaf ⟨(s.completed leaf).val, current_live s hc⟩ :=
  Or.inr ⟨hc,rfl⟩

theorem current_future_iff (s : State L M ell) {leaf : Leaf L}
    (hc : TaskState.current s = some leaf) (j : Fin M) :
    ¬MarkSupplied s leaf j ↔ (s.completed leaf).val<j.val := by
  simp only [MarkSupplied, TaskDisclosed, hc, true_and]
  omega

theorem subtree_nonempty (v : Node L) : (subtree v).Nonempty := by
  apply Finset.card_pos.mp
  rw [subtree_card]
  positivity

theorem lastChildClosed_empty : LastChildClosed (∅ : Retired L) := by
  intro v hv h
  obtain ⟨leaf,hl⟩ := subtree_nonempty (child v hv (Fin.last 7))
  exact False.elim (Finset.not_mem_empty leaf (h hl))

theorem initial_lastChildClosed (hM : 0<M) :
    LastChildClosed (TaskState.retired (initial : State L M ell)) := by
  have he : TaskState.retired (initial : State L M ell) = ∅ := by
    ext leaf
    simp only [TaskState.mem_retired, initial, Fin.val_zero, Finset.not_mem_empty, iff_false]
    omega
  rw [he]
  exact lastChildClosed_empty

theorem last_completion_hidden {s : State L M ell}
    (hs : LastChildClosed (TaskState.retired s)) {v : Node L} (hv : v.1.val<L)
    (hn : ¬NodeDisclosed s v) : ¬CompletionDisclosed s v hv (Fin.last 7) :=
  fun h => hn (hs v hv h)

end GradientHessian.GeometricDisclosure
