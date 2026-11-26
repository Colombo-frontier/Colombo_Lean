import GradientHessian.GeometricTerminalMisses
import GradientHessian.LocalizedMissJets
import GradientHessian.MemoryMissJets
import GradientHessian.GeometricRepairInvariant

/-! Terminal hidden-block conclusions for the actual full physical second
jets. The first and second derivatives are obtained from the literal scalar
functions after shared-coordinate projection. -/

noncomputable section
namespace GradientHessian.GeometricRepair
universe u
open Classical FrontierState TaskState GeometricDisclosure HigherHierarchy ComparisonController
open JetLocality EuclideanRegisters

variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

def oldBlockProjection (i : Fin 8) : Space Y E H m t →L[ℝ]
    Registers E (FirstHeight.depth (m+1)+2) :=
  (Inner.taskProjection (Y := Leaf.Space Y E (m+1)) (E := E) 8 (FirstHeight.depth (m+1)) i).comp
    (HierarchyAddresses.oldProjection t)

def innerBlockProjection (task : Fin (m+1)) : Space Y E H m t →L[ℝ]
    Registers E (Inner.absoluteDepth+2) :=
  (Inner.taskProjection (Y := Y) (E := E) (m+1) Inner.absoluteDepth task).comp
    (HierarchyAddresses.leafProjection t)

variable (K : ℝ) (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
  (p : Pending (Space Y E H m t)) (ht : choose (rules K data) p s=none)
include ht

theorem terminal_localized_jets (h : Fin t) (path : Fin (t-(h.val+1)) → Fin 8) (i : Fin 8)
    (hv : Visible (TaskState.retired s) (localNode h path))
    (hu : ¬NodeDisclosed s (localChild h path i)) :
    richJet (fun Z => Localized.potential (radius m K h.val) (width m h.val)
      (localCenter K data h path i) (localProjection h i Z)) p.point =
      richJet (fun Z => Localized.publicPotential (radius m K h.val) (localProjection h i Z)) p.point ∧
    richJet (fun Z => Localized.port (width m h.val)
      (localCenter K data h path i) (localProjection h i Z)) p.point=0 := by
  have hm := terminal_localized_miss K data s p ht h path i hv hu
  exact ⟨LocalizedMissJets.potential_richJet_public _ _ _ _ (width_pos m h.val) hm,
    LocalizedMissJets.port_richJet_zero _ _ _ (width_pos m h.val) hm⟩

theorem terminal_old_block_jets (path : Fin t → Fin 8) (i : Fin 8)
    (hv : Visible (TaskState.retired s) (oldNode path))
    (hu : ¬NodeDisclosed s (oldChild path i)) :
    richJet (fun Z => Inner.block (oldDirection data path i) (oldBlockProjection i Z)) p.point =
      richJet (fun Z => LatchChain.publicQuadratic (FirstHeight.depth (m+1)+1)
        (Inner.radius (FirstHeight.depth (m+1))) (oldBlockProjection i Z)) p.point ∧
    richJet (fun Z => Inner.completion (oldDirection data path i) (oldBlockProjection i Z)) p.point=0 := by
  have hm (j) := terminal_old_miss K data s p ht path i j hv hu
  exact ⟨MemoryMissJets.self_richJet_public _ _ _ _ (fun j => (Inner.radius_pos _ j).ne') _ hm,
    MemoryMissJets.port_richJet_zero _ _ _ _ _ (hm _)⟩

theorem terminal_inner_block_jets (leaf : Leaf (t+1)) (task : Fin (m+1))
    (hc : TaskState.current s=some leaf) (hu : ¬TaskDisclosed s leaf task) :
    richJet (fun Z => Inner.block ((leafCoefficients data leaf).v task)
      (innerBlockProjection task Z)) p.point =
      richJet (fun Z => LatchChain.publicQuadratic (Inner.absoluteDepth+1)
        (Inner.radius Inner.absoluteDepth) (innerBlockProjection task Z)) p.point ∧
    richJet (fun Z => Inner.completion ((leafCoefficients data leaf).v task)
      (innerBlockProjection task Z)) p.point=0 := by
  have hm (j) := terminal_inner_miss K data s p ht leaf task j hc hu
  exact ⟨MemoryMissJets.self_richJet_public _ _ _ _ (fun j => (Inner.radius_pos _ j).ne') _ hm,
    MemoryMissJets.port_richJet_zero _ _ _ _ _ (hm _)⟩

theorem terminal_future_gate_jet (leaf : Leaf (t+1)) (task : Fin (m+1))
    (hc : TaskState.current s=some leaf) (hu : ¬MarkSupplied s leaf task) :
    richJet (fun Z => InverseGate.gate ((leafCoefficients data leaf).a task)
      (HierarchyAddresses.numericalProjection t Z)) p.point=0 :=
  BoundedNumericalTest.miss_after_linear_richJet _ _ _
    (terminal_future_mark_miss K data s p ht leaf task hc hu)

omit ht K in
theorem current_miss_gate_jet (leaf : Leaf (t+1)) (hc : TaskState.current s=some leaf)
    (hh : hit data s p.point=false) :
    richJet (fun Z => InverseGate.gate ((leafCoefficients data leaf).a
      ⟨(s.completed leaf).val,current_live s hc⟩) (HierarchyAddresses.numericalProjection t Z)) p.point=0 :=
  BoundedNumericalTest.miss_after_linear_richJet _ _ _ (current_mark_miss data s p leaf hc hh)

theorem terminal_current_leaf_outgoing_zero (leaf : Leaf (t+1)) (hc : TaskState.current s=some leaf) :
    richJet (fun Z => Leaf.outgoing (leafCoefficients data leaf).v
      (HierarchyAddresses.leafProjection t Z)) p.point=0 := by
  have hu : ¬TaskDisclosed s leaf (Fin.last m) := by
    have hl := current_live s hc
    unfold TaskDisclosed
    simp only [Fin.val_last]
    omega
  exact (terminal_inner_block_jets K data s p ht leaf (Fin.last m) hc hu).2

end GradientHessian.GeometricRepair
