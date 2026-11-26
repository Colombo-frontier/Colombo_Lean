import GradientHessian.NumericalCoefficientPatch
import GradientHessian.CensoredMarkOrder

/-! Before target-mark supply, an active different leaf precedes the target.
This derives the numerical coefficient erasure side condition from the
literal controller guard, without restricting its retirement pattern. -/

noncomputable section
namespace GradientHessian.NumericalFrontierOrder
open HigherHierarchy CensoredHierarchy NumericalCoefficientPatch ControllerCensor
  HierarchyAddresses FrontierState TaskState

theorem futureLeaf_of_future {m : ℕ} : ∀ t (p : Plan m t) (i : LeafSlot t) (j : Fin (m+1)),
    CensoredMark.Future t p i j → selectedLeaf m t p≠i → FutureLeaf t p i
  | 0,p,i,j,hf,hn => by
    rcases hf with hl | ⟨he,_⟩
    · exact hl
    · exact False.elim (hn he)
  | t+1,p,i,j,hf,hn => by
    rcases hf with hl | ⟨he,hf⟩
    · exact Or.inl hl
    · exact Or.inr ⟨he,futureLeaf_of_future t p.2.2 i.2 j hf (fun ht => hn (Prod.ext he ht))⟩

theorem futureLeaf_before_supply {t m ell : ℕ} (before after : State (t+1) (m+1) ell)
    (cur target : Leaf (t+1)) (hc : TaskState.current before=some cur) (j : Fin (m+1))
    (hs : ComparisonControllerReplay.markSupplied target j before=false) (hne : cur≠target) :
    FutureLeaf t (planAt before after cur hc t) ((leafEquiv t).symm target) := by
  apply futureLeaf_of_future t _ _ j (CensoredMark.future_controller before after cur target hc j hs)
  rw [selectedLeaf_plan]
  exact fun he => hne ((leafEquiv t).symm.injective he)

theorem leafMask_current {t m ell : ℕ} (before after : State (t+1) (m+1) ell)
    (cur : Leaf (t+1)) (hc : TaskState.current before=some cur) :
    leafMask t (planAt before after cur hc t)=CensoredLeaf.stateMask before after cur hc := by
  suffices hh : ∀ h,leafMask h (planAt before after cur hc h)=CensoredLeaf.stateMask before after cur hc from hh t
  intro h
  induction h with
  | zero => rfl
  | succ h ih => exact ih

theorem current_index_before_supply {t m ell : ℕ} (before after : State (t+1) (m+1) ell)
    (leaf : Leaf (t+1)) (hc : TaskState.current before=some leaf) (j : Fin (m+1))
    (hs : ComparisonControllerReplay.markSupplied leaf j before=false) :
    (leafMask t (planAt before after leaf hc t)).current<j := by
  have hn := of_decide_eq_false hs
  rw [leafMask_current]
  change (⟨(before.completed leaf).val,TaskState.current_live before hc⟩ : Fin (m+1))<j
  change (before.completed leaf).val<j.val
  by_contra h
  exact hn (Or.inr ⟨hc,by omega⟩)

end GradientHessian.NumericalFrontierOrder
