import GradientHessian.CensoredMarkView
import GradientHessian.ControllerCensorPlan
import GradientHessian.ComparisonControllerReplay

/-! The future-prefix condition is a consequence of the actual current leaf
and the supply stopping rule, not an additional oracle-independence premise. -/

noncomputable section
namespace GradientHessian.CensoredMark
open Classical HigherHierarchy HierarchyAddresses CensoredHierarchy
  ControllerCensor FrontierState TaskState ComparisonControllerReplay

def selectedTask {m : ℕ} : (t : ℕ) → Plan m t → Fin (m+1)
  | 0,p => p.2.2.current
  | t+1,p => selectedTask t p.2.2

theorem future_of_same {m : ℕ} : ∀ t (p : Plan m t) (j : Fin (m+1)),
    selectedTask t p < j → Future t p (selectedLeaf m t p) j
  | 0,_,_,hj => Or.inr ⟨rfl,hj⟩
  | t+1,p,j,hj => Or.inr ⟨rfl,future_of_same t p.2.2 j hj⟩

theorem future_of_lt {m : ℕ} : ∀ t (p : Plan m t) (i : LeafSlot t) (j : Fin (m+1)),
    leafEquiv t (selectedLeaf m t p) < leafEquiv t i → Future t p i j := by
  intro t
  induction t with
  | zero =>
    intro p i j hi
    change ∃ k : Fin 1,(∀ a,a<k → _ ) ∧ _ at hi
    obtain ⟨k,_,hk⟩ := hi
    exact Or.inl hk
  | succ t ih =>
    intro p i j hi
    change ∃ k : Fin (t+2),(∀ a,a<k → leafWord (t+1) (selectedLeaf m (t+1) p) a=leafWord (t+1) i a) ∧
      leafWord (t+1) (selectedLeaf m (t+1) p) k<leafWord (t+1) i k at hi
    obtain ⟨k,he,hk⟩ := hi
    revert he hk
    refine Fin.cases ?_ (fun a => ?_) k
    · intro he hk
      exact Or.inl hk
    · intro he hk
      have hhead : p.1=i.1 := he 0 (by simp)
      apply Or.inr
      refine ⟨hhead,ih p.2.2 i.2 j ?_⟩
      change ∃ k : Fin (t+1),(∀ b,b<k → leafWord t (selectedLeaf m t p.2.2) b=leafWord t i.2 b) ∧
        leafWord t (selectedLeaf m t p.2.2) k<leafWord t i.2 k
      exact ⟨a,fun b hb => he b.succ (by simpa only [Fin.succ_lt_succ_iff] using hb),hk⟩

theorem selectedTask_planAt {t m ell : ℕ} (before after : State (t+1) (m+1) ell)
    (cur : Leaf (t+1)) (hc : TaskState.current before=some cur) (h : ℕ) :
    (selectedTask h (planAt before after cur hc h)).val=(before.completed cur).val := by
  induction h with
  | zero => rfl
  | succ h ih => exact ih

theorem future_controller {t m ell : ℕ} (before after : State (t+1) (m+1) ell)
    (cur target : Leaf (t+1)) (hc : TaskState.current before=some cur) (j : Fin (m+1))
    (hs : ComparisonControllerReplay.markSupplied target j before=false) :
    Future t (planAt before after cur hc t) ((leafEquiv t).symm target) j := by
  have hn := of_decide_eq_false hs
  have hnot : target∉TaskState.retired before := fun h => hn (Or.inl h)
  have hle : cur≤target := ((FrontierState.current_eq_some_iff _ _).mp hc).2 target hnot
  rcases lt_or_eq_of_le hle with hl | he
  · apply future_of_lt
    simpa only [selectedLeaf_plan,Equiv.apply_symm_apply] using hl
  · subst target
    rw [← selectedLeaf_plan before after cur hc]
    apply future_of_same
    have hj : (before.completed cur).val<j.val := by
      by_contra h
      exact hn (Or.inr ⟨hc,by omega⟩)
    change (selectedTask t (planAt before after cur hc t)).val<j.val
    simpa only [selectedTask_planAt] using hj

end GradientHessian.CensoredMark
