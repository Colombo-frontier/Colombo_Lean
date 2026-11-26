import GradientHessian.DirectionPolicyErasure
import GradientHessian.VisibilityTaskWindow

/-! Literal disclosure stops are monotone under completed-task increases.
Every actual repair trigger is evaluated strictly before its own stop. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical FrontierState TaskState TaskSlots GeometricDisclosure
  ComparisonController ComparisonControllerReplay VisibilityWindow VisibilityTaskWindow

variable {L M ell : ℕ}

theorem retired_mono_of_completed (s t : State L M ell)
    (hm : ∀ leaf,(s.completed leaf).val≤(t.completed leaf).val) :
    TaskState.retired s⊆TaskState.retired t := by
  intro leaf hl
  have hs := (mem_retired s leaf).mp hl
  apply (mem_retired t leaf).mpr
  have ht := (t.completed leaf).isLt
  have hh := hm leaf
  omega

theorem markSupplied_completed_mono (leaf : Leaf L) (j : Fin M) (s t : State L M ell)
    (hm : ∀ q,(s.completed q).val≤(t.completed q).val)
    (hs : ComparisonControllerReplay.markSupplied leaf j s=true) :
    ComparisonControllerReplay.markSupplied leaf j t=true := by
  have hr := retired_mono_of_completed s t hm
  apply decide_eq_true
  rcases of_decide_eq_true hs with hl | ⟨hc,hj⟩
  · exact Or.inl (hr hl)
  · by_cases hl : leaf∈TaskState.retired t
    · exact Or.inl hl
    · exact Or.inr ⟨current_preserved hr hc hl,hj.trans (hm leaf)⟩

theorem taskDisclosed_completed_mono (leaf : Leaf L) (j : Fin M) (s t : State L M ell)
    (hm : ∀ q,(s.completed q).val≤(t.completed q).val)
    (hs : ComparisonControllerReplay.taskDisclosed leaf j s=true) :
    ComparisonControllerReplay.taskDisclosed leaf j t=true := by
  apply decide_eq_true
  exact (of_decide_eq_true hs).trans_le (hm leaf)

theorem nodeStop_completed_mono (v : Node L) (s t : State L M ell)
    (hm : ∀ q,(s.completed q).val≤(t.completed q).val)
    (hs : DirectionPolicy.nodeStop v s=true) : DirectionPolicy.nodeStop v t=true := by
  apply decide_eq_true
  exact (of_decide_eq_true hs).trans (retired_mono_of_completed s t hm)

def actionStop {t m : ℕ} : Action t m → State (t+1) (m+1) ell → Bool
  | .localized h w i => DirectionPolicy.nodeStop (localChild h w i)
  | .old w i _ => DirectionPolicy.nodeStop (oldChild w i)
  | .inner leaf j _ => ComparisonControllerReplay.taskDisclosed leaf j
  | .futureMark leaf j => ComparisonControllerReplay.markSupplied leaf j

theorem actionStop_completed_mono {t m : ℕ} (a : Action t m) (s u : State (t+1) (m+1) ell)
    (hm : ∀ leaf,(s.completed leaf).val≤(u.completed leaf).val)
    (hs : actionStop a s=true) : actionStop a u=true := by
  cases a with
  | localized h w i => exact nodeStop_completed_mono (localChild h w i) s u hm hs
  | old w i j => exact nodeStop_completed_mono (oldChild w i) s u hm hs
  | inner leaf j k => exact taskDisclosed_completed_mono leaf j s u hm hs
  | futureMark leaf j => exact markSupplied_completed_mono leaf j s u hm hs

theorem actionStop_open_predecessor {t m : ℕ} (a : Action t m) (s u : State (t+1) (m+1) ell)
    (hm : ∀ leaf,(s.completed leaf).val≤(u.completed leaf).val)
    (hu : actionStop a u=false) : actionStop a s=false := by
  cases hs : actionStop a s with
  | false => rfl
  | true => have hh := actionStop_completed_mono a s u hm hs; simp [hu] at hh

theorem actionStop_retireNode_mono {t m : ℕ} (a : Action t m) (s : State (t+1) (m+1) ell)
    (v : Node (t+1)) (hs : actionStop a s=true) : actionStop a (retireNode s v)=true :=
  actionStop_completed_mono a s (retireNode s v) (retireSet_completed_mono s (subtree v)) hs

theorem actionStop_normal_mono {t m : ℕ} {X A : Type*} (a : Action t m)
    (R : Rules (t+1) (m+1) ell X A) (p : Pending X) (s : State (t+1) (m+1) ell)
    (hs : Ready s) (hstop : actionStop a s=true) : actionStop a (normal R p s)=true :=
  actionStop_completed_mono a s (normal R p s) (normal_completed_mono R p hs) hstop

theorem actionStop_serve_mono {t m : ℕ} {X A : Type*} (a : Action t m)
    (R : Rules (t+1) (m+1) ell X A) (p : Pending X) (s : State (t+1) (m+1) ell)
    (hs : Ready s) (hstop : actionStop a s=true) : actionStop a (serve R p s).afterNormal=true :=
  actionStop_completed_mono a s _ (serve_completed_mono R p hs) hstop

section ActualTrigger
universe u
variable {Y E : Type u} {H : ℕ → Type u} {t m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

theorem trigger_actionStop_false (K : ℝ) (data : HigherHierarchy.Data Y E H m t)
    (s : State (t+1) (m+1) ell) (Z : HigherHierarchy.Space Y E H m t) (a : Action t m)
    (ht : trigger K data s Z a=true) : actionStop a s=false := by
  cases a with
  | localized h w i =>
    simp only [trigger,decide_eq_true_eq] at ht
    exact decide_eq_false ht.2.1
  | old w i j =>
    simp only [trigger,decide_eq_true_eq] at ht
    exact decide_eq_false ht.2.1
  | inner leaf j k =>
    simp only [trigger,decide_eq_true_eq] at ht
    apply decide_eq_false
    exact ht.2.1
  | futureMark leaf j =>
    simp only [trigger,decide_eq_true_eq] at ht
    have hj := (current_future_iff s ht.1 j).mp ht.2.1
    apply decide_eq_false
    rintro (hr | ⟨_,hle⟩)
    · exact ((FrontierState.current_eq_some_iff _ _).mp ht.1).1 hr
    · exact (not_le_of_gt hj) hle

theorem chosen_actionStop_false (K : ℝ) (data : HigherHierarchy.Data Y E H m t)
    (s : State (t+1) (m+1) ell) (p : Pending (HigherHierarchy.Space Y E H m t))
    (a : Action t m) (ha : choose (rules K data) p s=some a) : actionStop a s=false :=
  trigger_actionStop_false K data s p.point a (choose_spec (rules K data) p s ha).2.1

end ActualTrigger
end GradientHessian.GeometricRepair
