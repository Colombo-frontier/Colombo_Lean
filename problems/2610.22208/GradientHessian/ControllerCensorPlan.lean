import GradientHessian.CensoredHierarchy
import GradientHessian.CensoredLeafController
import GradientHessian.ComparisonControllerInvariant
import GradientHessian.GeometricTerminalPlateaus

/-! The recursive scalar censor plan is determined by the pre-normal
current leaf and post-normal disclosure state. Addresses index coefficient
subtrees; each physical projection remains shared by all siblings. -/

noncomputable section
namespace GradientHessian.ControllerCensor
open Classical FrontierState TaskState TaskSlots GeometricDisclosure

variable {t m ell : ℕ}

def pathPrefix (leaf : Leaf (t+1)) (h : ℕ) : Fin (t-h) → Fin 8 :=
  fun i => leaf ⟨i.val,by have := i.isLt; omega⟩

def nodeAt (leaf : Leaf (t+1)) (h : ℕ) : Node (t+1) :=
  ⟨⟨t-h,by omega⟩,pathPrefix leaf h⟩

theorem nodeAt_internal (leaf : Leaf (t+1)) (h : ℕ) : (nodeAt leaf h).1.val<t+1 := by
  change t-h<t+1
  omega

def childAt (leaf : Leaf (t+1)) (h : ℕ) (i : Fin 8) : Node (t+1) :=
  child (nodeAt leaf h) (nodeAt_internal leaf h) i

def currentChild (leaf : Leaf (t+1)) (h : ℕ) : Fin 8 := leaf ⟨t-h,by omega⟩

def known (after : State (t+1) (m+1) ell) (leaf : Leaf (t+1)) (h : ℕ) (i : Fin 8) : Bool :=
  decide (NodeDisclosed after (childAt leaf h i))

def planAt (before after : State (t+1) (m+1) ell) (leaf : Leaf (t+1))
    (hc : TaskState.current before=some leaf) : (h : ℕ) → CensoredHierarchy.Plan m h
  | 0 => (currentChild leaf 0,known after leaf 0,CensoredLeaf.stateMask before after leaf hc)
  | h+1 => (currentChild leaf (h+1),known after leaf (h+1),planAt before after leaf hc h)

theorem nodeAt_contains (leaf : Leaf (t+1)) (h : ℕ) : InSubtree (nodeAt leaf h) leaf :=
  fun _ => rfl

theorem currentChild_contains (leaf : Leaf (t+1)) (h : ℕ) :
    leaf ∈ subtree (childAt leaf h (currentChild leaf h)) := by
  apply (mem_subtree _ _).mpr
  exact (inSubtree_child_iff _ _ _ _).mpr ⟨nodeAt_contains leaf h,rfl⟩

theorem nodeAt_visible (before : State (t+1) (m+1) ell) (leaf : Leaf (t+1))
    (hc : TaskState.current before=some leaf) (h : ℕ) :
    Visible (TaskState.retired before) (nodeAt leaf h) := ⟨leaf,hc,nodeAt_contains leaf h⟩

theorem currentChild_hidden (before : State (t+1) (m+1) ell) (leaf : Leaf (t+1))
    (hc : TaskState.current before=some leaf) (h : ℕ) :
    ¬NodeDisclosed before (childAt leaf h (currentChild leaf h)) := by
  intro hd
  exact ((FrontierState.current_eq_some_iff _ _).mp hc).1 (hd (currentChild_contains leaf h))

theorem lastChild_hidden (before : State (t+1) (m+1) ell) (leaf : Leaf (t+1))
    (hc : TaskState.current before=some leaf) (hs : LastChildClosed (TaskState.retired before)) (h : ℕ) :
    ¬NodeDisclosed before (childAt leaf h (Fin.last 7)) :=
  last_completion_hidden hs (nodeAt_internal leaf h)
    (GeometricRepair.visible_not_disclosed before _ (nodeAt_visible before leaf hc h))

theorem known_false_hidden_before (before after : State (t+1) (m+1) ell)
    (hmono : TaskState.retired before⊆TaskState.retired after) (leaf : Leaf (t+1)) (h : ℕ)
    (i : Fin 8) (hi : known after leaf h i=false) : ¬NodeDisclosed before (childAt leaf h i) := by
  intro hd
  exact (of_decide_eq_false hi) (nodeDisclosed_mono hmono hd)

theorem earlier_child_known (before after : State (t+1) (m+1) ell)
    (hmono : TaskState.retired before⊆TaskState.retired after) (leaf : Leaf (t+1))
    (hc : TaskState.current before=some leaf) (h : ℕ) (i : Fin 8) (hi : i<currentChild leaf h) :
    known after leaf h i=true := by
  apply decide_eq_true
  exact (FrontierOrder.earlier_children_retired (TaskState.retired before)
    (nodeAt leaf h) (nodeAt_internal leaf h) hc
    (currentChild_contains leaf h) i hi).trans hmono

@[simp] theorem nodeAt_zero (leaf : Leaf (t+1)) : nodeAt leaf 0=GeometricRepair.oldNode (pathPrefix leaf 0) := rfl
@[simp] theorem childAt_zero (leaf : Leaf (t+1)) (i : Fin 8) :
    childAt leaf 0 i=GeometricRepair.oldChild (pathPrefix leaf 0) i := rfl

theorem nodeAt_succ (leaf : Leaf (t+1)) (h : Fin t) :
    nodeAt leaf (h.val+1)=GeometricRepair.localNode h (pathPrefix leaf (h.val+1)) := rfl

theorem childAt_succ (leaf : Leaf (t+1)) (h : Fin t) (i : Fin 8) :
    childAt leaf (h.val+1) i=GeometricRepair.localChild h (pathPrefix leaf (h.val+1)) i := rfl

theorem selectedLeaf_digit (before after : State (t+1) (m+1) ell) (leaf : Leaf (t+1))
    (hc : TaskState.current before=some leaf) : ∀ (h : ℕ) (hh : h≤t) (j : Fin (h+1)),
    HierarchyAddresses.leafWord h (CensoredHierarchy.selectedLeaf m h (planAt before after leaf hc h)) j =
      leaf ⟨t-h+j.val,by have := j.isLt; omega⟩
  | 0,hh,j => by
    have hj : j=0 := Fin.ext (by omega)
    subst j
    rfl
  | h+1,hh,j => by
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · change HierarchyAddresses.leafWord h
        (CensoredHierarchy.selectedLeaf m h (planAt before after leaf hc h)) i = _
      rw [selectedLeaf_digit before after leaf hc h (by omega)]
      apply congrArg leaf
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

theorem selectedLeaf_plan (before after : State (t+1) (m+1) ell) (leaf : Leaf (t+1))
    (hc : TaskState.current before=some leaf) :
    CensoredHierarchy.selectedLeaf m t (planAt before after leaf hc t)=(HierarchyAddresses.leafEquiv t).symm leaf := by
  apply (HierarchyAddresses.leafEquiv t).injective
  rw [Equiv.apply_symm_apply]
  funext j
  change HierarchyAddresses.leafWord t
    (CensoredHierarchy.selectedLeaf m t (planAt before after leaf hc t)) j=leaf j
  rw [selectedLeaf_digit before after leaf hc t le_rfl]
  apply congrArg leaf
  apply Fin.ext
  change t-t+j.val=j.val
  omega

end GradientHessian.ControllerCensor
