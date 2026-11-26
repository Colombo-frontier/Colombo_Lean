import GradientHessian.GeometricTerminalOutgoing

/-! Terminal support misses yield genuine open plateaus for the outgoing
ports along the current path, before any Taylor-jet truncation. -/

noncomputable section
namespace GradientHessian.GeometricRepair
universe u
open Classical FrontierState TaskState GeometricDisclosure HigherHierarchy ComparisonController
open Filter
open scoped Topology

variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

variable (K : ℝ) (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
  (p : Pending (Space Y E H m t)) (ht : choose (rules K data) p s=none)
include ht

theorem terminal_visible_localized_outgoing_zero_near
    (hs : LastChildClosed (TaskState.retired s)) (h : Fin t)
    (path : Fin (t-(h.val+1)) → Fin 8)
    (hv : Visible (TaskState.retired s) (localNode h path)) :
    (fun Z => outgoing K (h.val+1)
      (HierarchyAddresses.dataAtHeight t (h.val+1) (Nat.succ_le_of_lt h.isLt) path data)
      (HierarchyAddresses.dropHeight t (h.val+1) (Nat.succ_le_of_lt h.isLt) Z))
        =ᶠ[𝓝 p.point] fun _ => 0 := by
  have hu := last_completion_hidden hs (localNode_internal h path)
    (visible_not_disclosed s (localNode h path) hv)
  have hz := LocalizedMissJets.port_zero_near
    (localProjection (Y := Y) (E := E) (H := H) (m := m) h (Fin.last 7))
    (localCenter K data h path (Fin.last 7)) p.point (width_pos m h.val)
    (terminal_localized_miss K data s p ht h path (Fin.last 7) hv hu)
  exact hz

theorem terminal_visible_old_outgoing_zero_near (hs : LastChildClosed (TaskState.retired s))
    (path : Fin t → Fin 8) (hv : Visible (TaskState.retired s) (oldNode path)) :
    (fun Z => FirstHeight.sourceOutgoing (HierarchyAddresses.oldData t path data)
      (HierarchyAddresses.oldProjection t Z)) =ᶠ[𝓝 p.point] fun _ => 0 := by
  have hu := last_completion_hidden hs (oldNode_internal path)
    (visible_not_disclosed s (oldNode path) hv)
  exact terminal_old_port_zero_near K data s p ht path (Fin.last 7) hv hu

theorem terminal_current_leaf_outgoing_zero_near (leaf : Leaf (t+1))
    (hc : TaskState.current s=some leaf) :
    (fun Z => Leaf.outgoing (leafCoefficients data leaf).v
      (HierarchyAddresses.leafProjection t Z)) =ᶠ[𝓝 p.point] fun _ => 0 := by
  have hu : ¬TaskDisclosed s leaf (Fin.last m) := by
    have hl := current_live s hc
    unfold TaskDisclosed
    simp only [Fin.val_last]
    omega
  exact terminal_inner_port_zero_near K data s p ht leaf (Fin.last m) hc hu

end GradientHessian.GeometricRepair
