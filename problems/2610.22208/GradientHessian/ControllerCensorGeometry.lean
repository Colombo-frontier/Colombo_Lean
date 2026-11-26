import GradientHessian.HierarchyPrefixLaws

/-! Actual terminal repair tests imply the recursive censor geometry for
the plan formed from the genuine before/after normal-operation snapshots. -/

noncomputable section
namespace GradientHessian.ControllerCensor
universe u
open Classical FrontierState TaskState TaskSlots GeometricDisclosure GeometricRepair
  HigherHierarchy HierarchyAddresses ComparisonController CensoredHierarchy

variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

variable (K : ℝ) (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
  (p : Pending (Space Y E H m t)) (hs : Ready s)
  (ht : choose (rules K data) p s=none) (hclosed : LastChildClosed (TaskState.retired s))
  (leaf : Leaf (t+1)) (hc : TaskState.current s=some leaf)

include hs ht hclosed hc in
theorem terminal_base_geometry :
    BaseGeometry (oldData t (pathPrefix leaf 0) data)
      (planAt s (normal (rules K data) p s) leaf hc 0) (oldProjection t p.point) := by
  let after := normal (rules K data) p s
  let mask := CensoredLeaf.stateMask s after leaf hc
  have hm := VisibilityTaskWindow.normal_completed_mono (rules K data) p hs leaf
  have hret := ComparisonControllerInvariant.normal_retired_mono (rules K data) p hs
  have hv : Visible (TaskState.retired s) (oldNode (pathPrefix leaf 0)) := nodeAt_visible s leaf hc 0
  have hcur : ¬TaskDisclosed s leaf mask.current := lt_irrefl _
  have hlast : ¬TaskDisclosed s leaf (Fin.last m) := by
    have hl := current_live s hc
    change ¬m<(s.completed leaf).val
    omega
  refine ⟨CensoredLeaf.stateMask_past s after leaf hc hm,
    CensoredLeaf.stateMask_current s after leaf hc,?_,?_,?_,?_,?_,?_,?_⟩
  · have h := terminal_inner_miss K data s p ht leaf mask.current (Fin.last (Inner.absoluteDepth+1)) hc hcur
    simpa only [innerReadout,leafCoefficients_old,leafData] using h
  · have h := terminal_inner_miss K data s p ht leaf (Fin.last m) (Fin.last (Inner.absoluteDepth+1)) hc hlast
    simpa only [innerReadout,leafCoefficients_old,leafData] using h
  · intro i hi j
    have hn : ¬TaskDisclosed after leaf i := of_decide_eq_false hi
    have hn' : ¬TaskDisclosed s leaf i := fun h => hn (h.trans_le hm)
    have h := terminal_inner_miss K data s p ht leaf i j hc hn'
    simpa only [innerReadout,leafCoefficients_old,leafData] using h
  · intro hi
    have hh := CensoredLeaf.normal_hidden_current_miss (rules K data) p s leaf hc hi
    have h := BoundedNumericalTest.miss_gateArg
      ((leafCoefficients data leaf).a mask.current) (numericalProjection t p.point)
      (current_mark_miss data s p leaf hc hh)
    simpa only [leafCoefficients_old,leafData] using h
  · exact terminal_old_miss K data s p ht (pathPrefix leaf 0) (currentChild leaf 0)
      (Fin.last (FirstHeight.depth (m+1)+1)) hv (currentChild_hidden s leaf hc 0)
  · exact terminal_old_miss K data s p ht (pathPrefix leaf 0) (Fin.last 7)
      (Fin.last (FirstHeight.depth (m+1)+1)) hv (lastChild_hidden s leaf hc hclosed 0)
  · intro i hi j
    exact terminal_old_miss K data s p ht (pathPrefix leaf 0) i j hv
      (known_false_hidden_before s after hret leaf 0 i hi)

include hs ht hclosed hc in
theorem terminal_geometry_at : ∀ (h : ℕ) (hh : h≤t),
    Geometry K h (planAt s (normal (rules K data) p s) leaf hc h)
      (dataAtHeight t h hh (pathPrefix leaf h) data) (dropHeight t h hh p.point)
  | 0,hh => terminal_base_geometry K data s p hs ht hclosed leaf hc
  | h+1,hh => by
    let level : Fin t := ⟨h,by omega⟩
    have hv : Visible (TaskState.retired s) (localNode level (pathPrefix leaf (h+1))) :=
      nodeAt_visible s leaf hc (h+1)
    have hret := ComparisonControllerInvariant.normal_retired_mono (rules K data) p hs
    refine ⟨?_,?_,?_,?_⟩
    · exact terminal_localized_miss K data s p ht level (pathPrefix leaf (h+1))
        (currentChild leaf (h+1)) hv (currentChild_hidden s leaf hc (h+1))
    · exact terminal_localized_miss K data s p ht level (pathPrefix leaf (h+1))
        (Fin.last 7) hv (lastChild_hidden s leaf hc hclosed (h+1))
    · intro i hi
      exact terminal_localized_miss K data s p ht level (pathPrefix leaf (h+1)) i hv
        (known_false_hidden_before s (normal (rules K data) p s) hret leaf (h+1) i hi)
    · change Geometry K h (planAt s (normal (rules K data) p s) leaf hc h)
        ((dataAtHeight t (h+1) hh (pathPrefix leaf (h+1)) data).children (currentChild leaf (h+1)))
        (lower (Space Y E H m h) (H h) (dropHeight t (h+1) hh p.point))
      rw [← dataAtHeight_current_child hh,← dropHeight_lower hh]
      exact terminal_geometry_at h (by omega)

include hs ht hclosed hc in
theorem terminal_geometry :
    Geometry K t (planAt s (normal (rules K data) p s) leaf hc t) data p.point := by
  have h := terminal_geometry_at K data s p hs ht hclosed leaf hc t le_rfl
  simpa only [dataAtHeight_self,dropHeight_self] using h

include hs ht hclosed hc in
theorem terminal_richJet (hK : 0<K) :
    JetLocality.richJet (HigherHierarchy.scalar K t data) p.point =
      JetLocality.richJet (CensoredHierarchy.scalar K t
        (planAt s (normal (rules K data) p s) leaf hc t) data) p.point :=
  CensoredHierarchy.richJet_eq hK t _ data p.point
    (terminal_geometry K data s p hs ht hclosed leaf hc)

omit ht hc in
include hs hclosed in
theorem serve_geometry
    (hcur : TaskState.current (serve (rules K data) p s).beforeNormal=some leaf) :
    Geometry K t
      (planAt (serve (rules K data) p s).beforeNormal (serve (rules K data) p s).afterNormal leaf hcur t)
      data p.point :=
  terminal_geometry K data (serve (rules K data) p s).beforeNormal p
    (repairRun_ready (rules K data) p (8^(t+1)) hs) (serve_terminal (rules K data) p s)
    (serve_lastChildClosed K data p s hclosed).1 leaf hcur

omit ht hc in
include hs hclosed in
theorem serve_richJet (hK : 0<K)
    (hcur : TaskState.current (serve (rules K data) p s).beforeNormal=some leaf) :
    JetLocality.richJet (HigherHierarchy.scalar K t data) p.point =
      JetLocality.richJet (CensoredHierarchy.scalar K t
        (planAt (serve (rules K data) p s).beforeNormal (serve (rules K data) p s).afterNormal leaf hcur t) data)
        p.point :=
  CensoredHierarchy.richJet_eq hK t _ data p.point (serve_geometry K data s p hs hclosed leaf hcur)

end GradientHessian.ControllerCensor
