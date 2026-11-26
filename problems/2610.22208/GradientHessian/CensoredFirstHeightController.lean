import GradientHessian.CensoredFirstHeight
import GradientHessian.ComparisonControllerInvariant

/-! The first-height scalar censor is instantiated by the literal geometric
controller. The normal operation reveals a current task or leaf only once;
the reply continues to use the pre-normal current child. -/

noncomputable section
namespace GradientHessian.CensoredFirstHeight
universe u
open Classical FrontierState TaskState TaskSlots ComparisonController GeometricDisclosure GeometricRepair
open JetLocality Filter
open scoped Topology

variable {Y E : Type u} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m ell : ℕ}

def emptyPath : Fin 0 → Fin 8 := fun j => Fin.elim0 j

theorem leaf_mem_oldChild (i : Fin 8) :
    HierarchyAddresses.leafEquiv 0 i ∈ subtree (oldChild emptyPath i) := by
  apply (mem_subtree _ _).mpr
  apply (inSubtree_child_iff _ _ _ _).mpr
  exact ⟨fun j => Fin.elim0 j,rfl⟩

theorem current_old_visible (s : State 1 (m+1) ell) (leaf : FrontierState.Leaf 1)
    (hc : TaskState.current s=some leaf) : Visible (TaskState.retired s) (oldNode emptyPath) :=
  ⟨leaf,hc,fun j => Fin.elim0 j⟩

def knownOuter (s : State 1 (m+1) ell) (i : Fin 8) : Bool :=
  decide (HierarchyAddresses.leafEquiv 0 i ∈ TaskState.retired s)

def controllerScalar (K : ℝ) (d : FirstHeight.Data Y E m) (s : State 1 (m+1) ell)
    (p : Pending (FirstHeight.SourceSpace Y E m)) (leaf : FrontierState.Leaf 1)
    (hc : TaskState.current s=some leaf) : FirstHeight.SourceSpace Y E m → ℝ :=
  scalar d (leaf 0) (knownOuter (normal (rules (Y := Y) (E := E) (H := fun _ => E) (t := 0) (m := m) K d) p s))
    (CensoredLeaf.stateMask s (normal (rules (Y := Y) (E := E) (H := fun _ => E) (t := 0) (m := m) K d) p s) leaf hc)

theorem terminal_richJet (K : ℝ) (d : FirstHeight.Data Y E m) (s : State 1 (m+1) ell)
    (p : Pending (FirstHeight.SourceSpace Y E m)) (hs : Ready s)
    (ht : choose (rules (Y := Y) (E := E) (H := fun _ => E) (t := 0) (m := m) K d) p s=none)
    (leaf : FrontierState.Leaf 1) (hc : TaskState.current s=some leaf) :
    richJet (FirstHeight.sourceNode d) p.point=richJet (controllerScalar K d s p leaf hc) p.point := by
  let R := rules (Y := Y) (E := E) (H := fun _ => E) (t := 0) (m := m) (ell := ell) K d
  let after := normal R p s
  have hv := current_old_visible s leaf hc
  have he : HierarchyAddresses.leafEquiv 0 (leaf 0)=leaf :=
    (HierarchyAddresses.leafEquiv 0).apply_symm_apply leaf
  have hu : ¬NodeDisclosed s (oldChild emptyPath (leaf 0)) := by
    intro hd
    have hm := hd (leaf_mem_oldChild (leaf 0))
    rw [he] at hm
    exact ((FrontierState.current_eq_some_iff _ _).mp hc).1 hm
  apply richJet_eq d (leaf 0) (knownOuter after) _ p.point
  · exact terminal_old_port_zero_near (Y := Y) (E := E) (H := fun _ => E) (t := 0) (m := m) K d s p ht emptyPath (leaf 0) hv hu
  · exact terminal_current_leaf_outgoing_zero_near (Y := Y) (E := E) (H := fun _ => E) (t := 0) (m := m) K d s p ht leaf hc
  · intro i hi j
    have hn : ¬HierarchyAddresses.leafEquiv 0 i ∈ TaskState.retired after := of_decide_eq_false hi
    have hpre : ¬NodeDisclosed s (oldChild emptyPath i) := by
      intro hd
      exact hn (ComparisonControllerInvariant.normal_retired_mono R p hs (hd (leaf_mem_oldChild i)))
    exact terminal_old_miss (Y := Y) (E := E) (H := fun _ => E) (t := 0) (m := m) K d s p ht emptyPath i j hv hpre
  · exact CensoredLeaf.terminal_physical_leaf_richJet (Y := Y) (E := E) (H := fun _ => E) (t := 0) (m := m) K d s p hs ht leaf hc

end GradientHessian.CensoredFirstHeight
