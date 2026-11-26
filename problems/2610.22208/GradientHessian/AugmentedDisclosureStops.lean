import GradientHessian.AugmentedDisclosure

/-! The full disclosure packet uses literal mark supply, including readouts
already disclosed in a task prefix. Its stop is monotone on all controller
states and implies the earlier replay stop whenever it remains open. -/

noncomputable section
namespace GradientHessian.AugmentedDisclosure
open Classical FrontierState TaskState TaskSlots GeometricDisclosure GeometricRepair
  ComparisonController ComparisonControllerReplay VisibilityWindow VisibilityTaskWindow

variable {L M ell : ℕ}

def markStop (leaf : Leaf L) (j : Fin M) (s : State L M ell) : Bool := decide (MarkSupplied s leaf j)

theorem markStop_open (leaf : Leaf L) (j : Fin M) (s : State L M ell)
    (hs : markStop leaf j s=false) : ComparisonControllerReplay.markSupplied leaf j s=false := by
  apply decide_eq_false
  have hn : ¬MarkSupplied s leaf j := of_decide_eq_false hs
  rintro (hl | ⟨hc,hj⟩)
  · exact hn (Or.inl (retired_all_tasks_disclosed hl j))
  · rcases lt_or_eq_of_le hj with hj | hj
    · exact hn (Or.inl hj)
    · exact hn (Or.inr ⟨hc,hj⟩)

theorem markStop_completed_mono (leaf : Leaf L) (j : Fin M) (s u : State L M ell)
    (hm : ∀ q,(s.completed q).val≤(u.completed q).val) (hs : markStop leaf j s=true) :
    markStop leaf j u=true := by
  apply decide_eq_true
  rcases of_decide_eq_true hs with hj | ⟨hc,hj⟩
  · exact Or.inl (hj.trans_le (hm leaf))
  · have hle : j.val≤(u.completed leaf).val := hj.le.trans (hm leaf)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl hlt
    · apply Or.inr
      refine ⟨current_preserved (retired_mono_of_completed s u hm) hc ?_,heq⟩
      intro hr
      have hr' := (mem_retired u leaf).mp hr
      have hj' := j.isLt
      omega

theorem markStop_retireNode_mono (leaf : Leaf L) (j : Fin M) (s : State L M ell)
    (v : Node L) (hs : markStop leaf j s=true) : markStop leaf j (retireNode s v)=true :=
  markStop_completed_mono leaf j s _ (retireSet_completed_mono s (subtree v)) hs

theorem markStop_normal_mono {X A : Type*} (leaf : Leaf L) (j : Fin M)
    (R : Rules L M ell X A) (p : Pending X) (s : State L M ell) (hs : Ready s)
    (hstop : markStop leaf j s=true) : markStop leaf j (normal R p s)=true :=
  markStop_completed_mono leaf j s _ (normal_completed_mono R p hs) hstop

end GradientHessian.AugmentedDisclosure
