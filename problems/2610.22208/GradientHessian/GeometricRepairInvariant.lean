import GradientHessian.GeometricRepairRules
import GradientHessian.GeometricRetirement

/-! Disclosure closure for the actual geometric controller, including the
single normal operation after its terminal repair pass. -/

noncomputable section
namespace GradientHessian.GeometricRepair
universe u
open Classical FrontierState TaskState TaskSlots GeometricDisclosure HigherHierarchy ComparisonController

variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

theorem trigger_preserves_lastChildClosed (K : ℝ) (data : Data Y E H m t)
    (s : State (t+1) (m+1) ell) (Z : Space Y E H m t) (a : Action t m)
    (hs : LastChildClosed (TaskState.retired s)) (ha : trigger K data s Z a=true) :
    LastChildClosed (TaskState.retired (retireNode s (target a))) := by
  rw [retireNode_retired]
  cases a with
  | localized h path i =>
    have hv : Visible (TaskState.retired s) (localNode h path) :=
      (of_decide_eq_true ha).1
    by_cases hi : i=Fin.last 7
    · simpa only [target,if_pos hi] using
        lastChildClosed_retire_visible hs (localNode h path) hv
    · simpa only [target,if_neg hi,localChild] using
        lastChildClosed_retire_nonlast hs (localNode h path) (localNode_internal h path) hv i hi
  | old path i j =>
    exact lastChildClosed_retire_visible hs (oldNode path) (of_decide_eq_true ha).1
  | inner leaf task j =>
    exact lastChildClosed_retire_visible hs (leafNode leaf)
      ⟨leaf,(of_decide_eq_true ha).1,fun _ => rfl⟩
  | futureMark leaf task =>
    exact lastChildClosed_retire_visible hs (leafNode leaf)
      ⟨leaf,(of_decide_eq_true ha).1,fun _ => rfl⟩

theorem repairRun_lastChildClosed (K : ℝ) (data : Data Y E H m t)
    (p : Pending (Space Y E H m t)) (n : ℕ) (s : State (t+1) (m+1) ell)
    (hs : LastChildClosed (TaskState.retired s)) :
    LastChildClosed (TaskState.retired (repairRun (rules K data) p n s).1) := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    cases hc : choose (rules K data) p s with
    | none => simpa [repairRun,hc] using hs
    | some a =>
      have ha := (choose_spec (rules K data) p s hc).2.1
      simpa only [repairRun,hc] using ih (retireNode s (target a))
        (trigger_preserves_lastChildClosed K data s p.point a hs ha)

end GradientHessian.GeometricRepair

namespace GradientHessian.GeometricDisclosure
open Classical FrontierState TaskState TaskSlots
variable {L M ell : ℕ}

theorem ordinaryStep_lastChildClosed (hit : Bool) (s : State L M ell)
    (hs : LastChildClosed (TaskState.retired s)) :
    LastChildClosed (TaskState.retired (ordinaryStep hit s)) := by
  cases hc : TaskState.current s with
  | none => simpa only [ordinaryStep,hc] using hs
  | some leaf =>
    have hcur : TaskState.current (advanceSlot s leaf)=some leaf := by
      simpa only [TaskState.current,advanceSlot_retired] using hc
    simp only [ordinaryStep,hc]
    split_ifs
    · rw [retired_completeLeaf _ _ (current_live _ hcur)]
      split_ifs
      · rw [advanceSlot_retired]
        exact lastChildClosed_retire_current hs hc
      · simpa only [advanceSlot_retired] using hs
    · simpa only [advanceSlot_retired] using hs

theorem richComplete_lastChildClosed (s : State L M ell)
    (hs : LastChildClosed (TaskState.retired s)) :
    LastChildClosed (TaskState.retired (richComplete s)) := by
  cases hc : TaskState.current s with
  | none => simpa only [richComplete,hc] using hs
  | some leaf =>
    rw [richComplete_retired s hc]
    exact lastChildClosed_retire_current hs hc

end GradientHessian.GeometricDisclosure

namespace GradientHessian.GeometricRepair
universe u
open Classical FrontierState TaskState GeometricDisclosure HigherHierarchy ComparisonController
variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

theorem normal_lastChildClosed (K : ℝ) (data : Data Y E H m t)
    (p : Pending (Space Y E H m t)) (s : State (t+1) (m+1) ell)
    (hs : LastChildClosed (TaskState.retired s)) :
    LastChildClosed (TaskState.retired (normal (rules K data) p s)) := by
  cases hk : p.kind
  · simpa only [normal,hk] using ordinaryStep_lastChildClosed (hit data s p.point) s hs
  · simpa only [normal,hk] using richComplete_lastChildClosed s hs

theorem serve_lastChildClosed (K : ℝ) (data : Data Y E H m t)
    (p : Pending (Space Y E H m t)) (s : State (t+1) (m+1) ell)
    (hs : LastChildClosed (TaskState.retired s)) :
    LastChildClosed (TaskState.retired (serve (rules K data) p s).beforeNormal) ∧
    LastChildClosed (TaskState.retired (serve (rules K data) p s).afterNormal) := by
  have hb := repairRun_lastChildClosed K data p (8^(t+1)) s hs
  exact ⟨hb,normal_lastChildClosed K data p _ hb⟩

end GradientHessian.GeometricRepair
