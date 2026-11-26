import GradientHessian.CensoredLeafAgreement
import GradientHessian.GeometricTerminalOutgoing
import GradientHessian.VisibilityTaskWindow
import GradientHessian.SecondJetPullback

/-! The current task is taken from the pre-normal snapshot, while permitted
coefficients are taken from the post-normal disclosure prefix. Terminality
of the actual geometric repair pass supplies every local miss used below. -/

noncomputable section
namespace GradientHessian.CensoredLeaf
open Classical FrontierState TaskState TaskSlots ComparisonController GeometricDisclosure
open JetLocality Filter InnerCoordinates
open scoped Topology

variable {L M ell : ℕ} {X Action : Type*}

def stateMask (before after : State L M ell) (leaf : FrontierState.Leaf L)
    (hc : TaskState.current before=some leaf) : Mask M where
  current := ⟨(before.completed leaf).val,current_live before hc⟩
  readout := decide (TaskDisclosed after leaf ⟨(before.completed leaf).val,current_live before hc⟩)
  memory := fun j => decide (TaskDisclosed after leaf j)

theorem stateMask_past (before after : State L M ell) (leaf : FrontierState.Leaf L)
    (hc : TaskState.current before=some leaf)
    (hm : (before.completed leaf).val≤(after.completed leaf).val) :
    ∀ i,i<(stateMask before after leaf hc).current → (stateMask before after leaf hc).memory i=true := by
  intro i hi
  apply decide_eq_true
  have hi' : i.val<(before.completed leaf).val := hi
  exact hi'.trans_le hm

theorem stateMask_current (before after : State L M ell) (leaf : FrontierState.Leaf L)
    (hc : TaskState.current before=some leaf) :
    (stateMask before after leaf hc).readout=true →
      (stateMask before after leaf hc).memory (stateMask before after leaf hc).current=true := id

theorem stateMask_forcing_supplied (before after : State L M ell) (leaf : FrontierState.Leaf L)
    (hc : TaskState.current before=some leaf) (i : Fin M)
    (hi : i≤(stateMask before after leaf hc).current) : MarkSupplied before leaf i := by
  have hi' : i.val≤(before.completed leaf).val := hi
  rcases lt_or_eq_of_le hi' with h | h
  · exact Or.inl h
  · exact Or.inr ⟨hc,h⟩

theorem stateMask_readout_disclosed (before after : State L M ell) (leaf : FrontierState.Leaf L)
    (hc : TaskState.current before=some leaf)
    (hm : (before.completed leaf).val≤(after.completed leaf).val) (i : Fin M)
    (hi : i<(stateMask before after leaf hc).current ∨
      i=(stateMask before after leaf hc).current ∧ (stateMask before after leaf hc).readout=true) :
    TaskDisclosed after leaf i := by
  rcases hi with h | ⟨rfl,h⟩
  · have hi' : i.val<(before.completed leaf).val := h
    exact hi'.trans_le hm
  · exact of_decide_eq_true h

theorem stateMask_memory_disclosed (before after : State L M ell) (leaf : FrontierState.Leaf L)
    (hc : TaskState.current before=some leaf) (i : Fin M)
    (hi : (stateMask before after leaf hc).memory i=true) : TaskDisclosed after leaf i :=
  of_decide_eq_true hi

theorem normal_rich_retires (R : Rules L M ell X Action) (p : Pending X)
    (s : State L M ell) (leaf : FrontierState.Leaf L) (hc : TaskState.current s=some leaf)
    (hk : p.kind=.rich) : leaf ∈ TaskState.retired (normal R p s) := by
  simp only [normal,hk,richComplete_retired s hc,Finset.mem_insert_self]

theorem normal_hit_discloses (R : Rules L M ell X Action) (p : Pending X)
    (s : State L M ell) (leaf : FrontierState.Leaf L) (hc : TaskState.current s=some leaf)
    (hh : R.hit s p.point=true) :
    TaskDisclosed (normal R p s) leaf ⟨(s.completed leaf).val,current_live s hc⟩ := by
  have hl : ((advanceSlot s leaf).completed leaf).val<M := by simpa using current_live s hc
  cases hk : p.kind with
  | ordinary =>
    simp only [TaskDisclosed,normal,hk,ordinaryStep,hc,hh,Bool.true_or,if_true,
      completeLeaf_completed _ _ hl,advanceSlot_completed]
    omega
  | rich =>
    simpa only [TaskDisclosed,normal,hk,richComplete,hc,retireSet,Finset.mem_singleton,
      if_true,Fin.val_last] using current_live s hc

theorem normal_hidden_current_miss (R : Rules L M ell X Action) (p : Pending X)
    (s : State L M ell) (leaf : FrontierState.Leaf L) (hc : TaskState.current s=some leaf)
    (hh : (stateMask s (normal R p s) leaf hc).readout=false) : R.hit s p.point=false := by
  cases he : R.hit s p.point with
  | false => rfl
  | true =>
    have hd := normal_hit_discloses R p s leaf hc he
    have hx : (stateMask s (normal R p s) leaf hc).readout=true := decide_eq_true hd
    simp only [hx,Bool.true_eq_false] at hh

universe u
variable {Y E : Type u} {H : ℕ → Type u} {t m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

omit [InnerProductSpace ℝ Y] [InnerProductSpace ℝ E] in
theorem stateMask_view_congr (before after : State L M ell) (leaf : FrontierState.Leaf L)
    (hc : TaskState.current before=some leaf)
    (hm : (before.completed leaf).val≤(after.completed leaf).val) (θ η : Leaf.Marks Y E M)
    (hb : ∀ i,MarkSupplied before leaf i → θ.1 i=η.1 i)
    (ha : ∀ i,TaskDisclosed after leaf i → θ.2.1 i=η.2.1 i)
    (hv : ∀ i,TaskDisclosed after leaf i → θ.2.2 i=η.2.2 i) :
    view (stateMask before after leaf hc) θ=view (stateMask before after leaf hc) η :=
  view_congr _ θ η
    (fun i hi => hb i (stateMask_forcing_supplied before after leaf hc i hi))
    (fun i hi => ha i (stateMask_readout_disclosed before after leaf hc hm i hi))
    (fun i hi => hv i (stateMask_memory_disclosed before after leaf hc i hi))

def leafMarks (data : HigherHierarchy.Data Y E H m t) (leaf : FrontierState.Leaf (t+1)) :
    Leaf.Marks Y E (m+1) :=
  ((GeometricRepair.leafCoefficients data leaf).b,
    (GeometricRepair.leafCoefficients data leaf).a,(GeometricRepair.leafCoefficients data leaf).v)

theorem terminal_leaf_richJet (K : ℝ) (data : HigherHierarchy.Data Y E H m t)
    (s : State (t+1) (m+1) ell) (p : Pending (HigherHierarchy.Space Y E H m t))
    (hs : Ready s) (ht : choose (GeometricRepair.rules K data) p s=none)
    (leaf : FrontierState.Leaf (t+1)) (hc : TaskState.current s=some leaf) :
    richJet (Leaf.objective (GeometricRepair.leafCoefficients data leaf).A
      (GeometricRepair.leafCoefficients data leaf).b (GeometricRepair.leafCoefficients data leaf).a
      (GeometricRepair.leafCoefficients data leaf).v) (HierarchyAddresses.leafProjection t p.point)=
    richJet (objective (stateMask s (normal (GeometricRepair.rules K data) p s) leaf hc)
      (GeometricRepair.leafCoefficients data leaf).A (leafMarks data leaf))
      (HierarchyAddresses.leafProjection t p.point) := by
  let after := normal (GeometricRepair.rules K data) p s
  let mask := stateMask s after leaf hc
  have hmono := VisibilityTaskWindow.normal_completed_mono (GeometricRepair.rules K data) p hs leaf
  have hu : ¬TaskDisclosed s leaf mask.current := by
    change ¬(s.completed leaf).val<(s.completed leaf).val
    omega
  apply full_leaf_richJet_eq (by omega) mask _ (leafMarks data leaf) _
    (stateMask_past s after leaf hc hmono) (stateMask_current s after leaf hc)
  · exact MemoryMissJets.port_zero_near (Inner.absoluteDepth+1)
      (Inner.taskProjection (Y := Y) (E := E) (m+1) Inner.absoluteDepth mask.current)
      ((GeometricRepair.leafCoefficients data leaf).v mask.current) (Inner.radius Inner.absoluteDepth)
      (HierarchyAddresses.leafProjection t p.point)
      (GeometricRepair.terminal_inner_miss K data s p ht leaf mask.current _ hc hu)
  · intro i hi j
    have hn : ¬TaskDisclosed after leaf i := of_decide_eq_false hi
    have hn' : ¬TaskDisclosed s leaf i := fun h => hn (h.trans_le hmono)
    exact GeometricRepair.terminal_inner_miss K data s p ht leaf i j hc hn'
  · intro hh
    apply BoundedNumericalTest.miss_gateArg
    exact GeometricRepair.current_mark_miss data s p leaf hc
      (normal_hidden_current_miss (GeometricRepair.rules K data) p s leaf hc hh)

set_option maxHeartbeats 600000 in
theorem terminal_physical_leaf_richJet (K : ℝ) (data : HigherHierarchy.Data Y E H m t)
    (s : State (t+1) (m+1) ell) (p : Pending (HigherHierarchy.Space Y E H m t))
    (hs : Ready s) (ht : choose (GeometricRepair.rules K data) p s=none)
    (leaf : FrontierState.Leaf (t+1)) (hc : TaskState.current s=some leaf) :
    richJet ((Leaf.objective (GeometricRepair.leafCoefficients data leaf).A
      (GeometricRepair.leafCoefficients data leaf).b (GeometricRepair.leafCoefficients data leaf).a
      (GeometricRepair.leafCoefficients data leaf).v) ∘ HierarchyAddresses.leafProjection t) p.point=
    richJet ((objective (stateMask s (normal (GeometricRepair.rules K data) p s) leaf hc)
      (GeometricRepair.leafCoefficients data leaf).A (leafMarks data leaf)) ∘
        HierarchyAddresses.leafProjection t) p.point := by
  have hactual : ContDiff ℝ 2 (Leaf.objective (GeometricRepair.leafCoefficients data leaf).A
      (GeometricRepair.leafCoefficients data leaf).b (GeometricRepair.leafCoefficients data leaf).a
      (GeometricRepair.leafCoefficients data leaf).v) :=
    (Leaf.objective_contDiff (Y := Y) (E := E) (by omega) _ _ _ _).of_le (by decide)
  have hmasked : ContDiff ℝ 2 (objective
      (stateMask s (normal (GeometricRepair.rules K data) p s) leaf hc)
      (GeometricRepair.leafCoefficients data leaf).A (leafMarks data leaf)) :=
    (objective_contDiff (Y := Y) (E := E) (by omega) _ _ _).of_le (by decide)
  exact SecondJetPullback.richJet_comp_linear_eq (E := HigherHierarchy.Space Y E H m t)
    (F := Leaf.Space Y E (m+1)) (HierarchyAddresses.leafProjection t)
    hactual hmasked (terminal_leaf_richJet K data s p hs ht leaf hc)

end GradientHessian.CensoredLeaf
