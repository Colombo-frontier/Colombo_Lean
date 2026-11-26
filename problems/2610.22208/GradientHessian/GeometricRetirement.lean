import GradientHessian.GeometricDisclosure
import GradientHessian.FrontierOrder

/-! The last-child disclosure invariant is preserved by the actual kinds
of geometric retirement. It uses lexicographic frontier order, not values
of scalar ports at the selected point. -/

noncomputable section
namespace GradientHessian.GeometricDisclosure
open Classical FrontierState FrontierOrder

variable {L : ℕ}

theorem lastChildClosed_retire_visible {R : Retired L} (hR : LastChildClosed R)
    (v : Node L) (hv : Visible R v) : LastChildClosed (retireSubtree R v) := by
  obtain ⟨cur,hc,hcv⟩ := hv
  have hcv' := (mem_subtree _ _).mpr hcv
  intro w hw hlast
  by_cases hr : subtree (child w hw (Fin.last 7)) ⊆ R
  · exact (hR w hw hr).trans (subset_retireSubtree R v)
  · obtain ⟨a,ha⟩ := Finset.sdiff_nonempty.mpr hr
    have hal := (Finset.mem_sdiff.mp ha).1
    have har := (Finset.mem_sdiff.mp ha).2
    have hav : a ∈ subtree v := (Finset.mem_union.mp (hlast hal)).resolve_left har
    have haw := subtree_child_subset w hw (Fin.last 7) hal
    by_cases hd : v.1.val≤w.1.val
    · exact (subtree_subset_of_common_leaf v w hd hav haw).trans Finset.subset_union_right
    · have hd' : (child w hw (Fin.last 7)).1.val≤v.1.val := by simp only [child]; omega
      have hvl := subtree_subset_of_common_leaf (child w hw (Fin.last 7)) v hd' hal hav
      exact current_in_last_child_all_retired R (retireSubtree R v)
        (subset_retireSubtree R v) w hw hc (hvl hcv') hlast

theorem lastChildClosed_retire_nonlast {R : Retired L} (hR : LastChildClosed R)
    (v : Node L) (hv : v.1.val<L) (hvis : Visible R v) (i : Fin 8) (hi : i≠Fin.last 7) :
    LastChildClosed (retireSubtree R (child v hv i)) := by
  obtain ⟨cur,hc,hcv⟩ := hvis
  have hcv' := (mem_subtree _ _).mpr hcv
  intro w hw hlast
  by_cases hr : subtree (child w hw (Fin.last 7)) ⊆ R
  · exact (hR w hw hr).trans (subset_retireSubtree R _)
  · obtain ⟨a,ha⟩ := Finset.sdiff_nonempty.mpr hr
    have hal := (Finset.mem_sdiff.mp ha).1
    have har := (Finset.mem_sdiff.mp ha).2
    have hat : a ∈ subtree (child v hv i) := (Finset.mem_union.mp (hlast hal)).resolve_left har
    have hav := subtree_child_subset v hv i hat
    have haw := subtree_child_subset w hw (Fin.last 7) hal
    rcases lt_trichotomy v.1.val w.1.val with hd | hd | hd
    · have hdep : (child v hv i).1.val≤w.1.val := by simp only [child]; omega
      exact (subtree_subset_of_common_leaf (child v hv i) w hdep hat haw).trans
        Finset.subset_union_right
    · have hvi := ((inSubtree_child_iff v hv i a).mp ((mem_subtree _ _).mp hat)).2
      have hwi := ((inSubtree_child_iff w hw (Fin.last 7) a).mp ((mem_subtree _ _).mp hal)).2
      have hind : (⟨v.1.val,hv⟩ : Fin L)=⟨w.1.val,hw⟩ := Fin.ext hd
      rw [hind,hwi] at hvi
      exact False.elim (hi hvi.symm)
    · have hdep : (child w hw (Fin.last 7)).1.val≤v.1.val := by simp only [child]; omega
      have hvl := subtree_subset_of_common_leaf (child w hw (Fin.last 7)) v hdep hal hav
      exact current_in_last_child_all_retired R (retireSubtree R (child v hv i))
        (subset_retireSubtree R _) w hw hc (hvl hcv') hlast

theorem lastChildClosed_retire_current {R : Retired L} (hR : LastChildClosed R)
    {cur : Leaf L} (hc : current R=some cur) : LastChildClosed (insert cur R) := by
  have hv : Visible R (leafNode cur) := ⟨cur,hc,fun _ => rfl⟩
  have he : R ∪ {cur} = insert cur R := by ext a; simp [or_comm]
  simpa only [retireSubtree,subtree_leafNode,he] using
    lastChildClosed_retire_visible hR (leafNode cur) hv

end GradientHessian.GeometricDisclosure
