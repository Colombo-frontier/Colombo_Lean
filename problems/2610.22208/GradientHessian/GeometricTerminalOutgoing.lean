import GradientHessian.GeometricTerminalJets
import GradientHessian.GeometricMaskJets

/-! Every visible unfinished node has a zero outgoing second jet after
the actual repair pass. Future numerical forcing terms are erased with
their full selector weights, using the current unfinished task's plateau. -/

noncomputable section
namespace GradientHessian.GeometricRepair
universe u
open Classical FrontierState TaskState GeometricDisclosure HigherHierarchy ComparisonController
open Filter JetLocality EuclideanRegisters
open scoped Topology

variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

variable (K : ℝ) (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
  (p : Pending (Space Y E H m t)) (ht : choose (rules K data) p s=none)
include ht

theorem terminal_inner_port_zero_near (leaf : Leaf (t+1)) (task : Fin (m+1))
    (hc : TaskState.current s=some leaf) (hu : ¬TaskDisclosed s leaf task) :
    (fun Z => Inner.completion ((leafCoefficients data leaf).v task)
      (innerBlockProjection task Z)) =ᶠ[𝓝 p.point] fun _ => 0 :=
  MemoryMissJets.port_zero_near _ _ _ _ _
    (terminal_inner_miss K data s p ht leaf task (Fin.last (Inner.absoluteDepth+1)) hc hu)

theorem terminal_old_port_zero_near (path : Fin t → Fin 8) (i : Fin 8)
    (hv : Visible (TaskState.retired s) (oldNode path))
    (hu : ¬NodeDisclosed s (oldChild path i)) :
    (fun Z => Inner.completion (oldDirection data path i) (oldBlockProjection i Z)) =ᶠ[𝓝 p.point] fun _ => 0 :=
  MemoryMissJets.port_zero_near _ _ _ _ _
    (terminal_old_miss K data s p ht path i (Fin.last (FirstHeight.depth (m+1)+1)) hv hu)

omit ht K data p in
theorem visible_not_disclosed (v : Node (t+1)) (hv : Visible (TaskState.retired s) v) :
    ¬NodeDisclosed s v := by
  obtain ⟨leaf,hc,hl⟩ := hv
  intro hd
  exact ((FrontierState.current_eq_some_iff _ _).mp hc).1 (hd ((mem_subtree _ _).mpr hl))

theorem terminal_visible_localized_outgoing_zero
    (hs : LastChildClosed (TaskState.retired s)) (h : Fin t)
    (path : Fin (t-(h.val+1)) → Fin 8)
    (hv : Visible (TaskState.retired s) (localNode h path)) :
    richJet (fun Z => outgoing K (h.val+1)
      (HierarchyAddresses.dataAtHeight t (h.val+1) (Nat.succ_le_of_lt h.isLt) path data)
      (HierarchyAddresses.dropHeight t (h.val+1) (Nat.succ_le_of_lt h.isLt) Z)) p.point=0 := by
  have hu := last_completion_hidden hs (localNode_internal h path)
    (visible_not_disclosed s (localNode h path) hv)
  exact (terminal_localized_jets K data s p ht h path (Fin.last 7) hv hu).2

theorem terminal_visible_old_outgoing_zero (hs : LastChildClosed (TaskState.retired s))
    (path : Fin t → Fin 8) (hv : Visible (TaskState.retired s) (oldNode path)) :
    richJet (fun Z => FirstHeight.sourceOutgoing (HierarchyAddresses.oldData t path data)
      (HierarchyAddresses.oldProjection t Z)) p.point=0 := by
  have hu := last_completion_hidden hs (oldNode_internal path)
    (visible_not_disclosed s (oldNode path) hv)
  exact (terminal_old_block_jets K data s p ht path (Fin.last 7) hv hu).2

theorem terminal_future_weighted_forcing_zero (leaf : Leaf (t+1)) (task : Fin (m+1))
    (hc : TaskState.current s=some leaf) (hu : ¬MarkSupplied s leaf task) :
    richJet (fun Z => InnerSelector.weight
      (Inner.ports (leafCoefficients data leaf).v (HierarchyAddresses.leafProjection t Z)) task *
      Inner.payload (leafCoefficients data leaf).b (leafCoefficients data leaf).a
        (leafCoefficients data leaf).v (HierarchyAddresses.leafProjection t Z) task) p.point=0 := by
  let currentTask : Fin (m+1) := ⟨(s.completed leaf).val,current_live s hc⟩
  have hlt : currentTask<task := (current_future_iff s hc task).mp hu
  have hidden : ¬TaskDisclosed s leaf currentTask := by
    exact lt_irrefl _
  exact GeometricMaskJets.later_forcing_richJet_zero
    (fun j Z => Inner.ports (leafCoefficients data leaf).v (HierarchyAddresses.leafProjection t Z) j)
    (fun Z => Inner.payload (leafCoefficients data leaf).b (leafCoefficients data leaf).a
      (leafCoefficients data leaf).v (HierarchyAddresses.leafProjection t Z) task)
    hlt (terminal_inner_port_zero_near K data s p ht leaf currentTask hc hidden)

end GradientHessian.GeometricRepair
