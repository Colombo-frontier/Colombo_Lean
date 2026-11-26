import GradientHessian.GeometricRepairRules

/-! Terminality of the literal geometric repair pass implies each hidden
visible support/readout test is a genuine miss. No miss is assumed as an
additional field of the controller or its state. -/

noncomputable section
namespace GradientHessian.GeometricRepair
universe u
open Classical FrontierState TaskState GeometricDisclosure HigherHierarchy ComparisonController

variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]

variable (K : ℝ) (data : Data Y E H m t) (s : State (t+1) (m+1) ell)
  (p : Pending (Space Y E H m t)) (ht : choose (rules K data) p s=none)
include ht

theorem terminal_localized_miss (h : Fin t) (path : Fin (t-(h.val+1)) → Fin 8) (i : Fin 8)
    (hv : Visible (TaskState.retired s) (localNode h path))
    (hu : ¬NodeDisclosed s (localChild h path i)) :
    3*width m h.val < ‖localProjection h i p.point-localCenter K data h path i‖ := by
  have hn := of_decide_eq_false (terminal_trigger_false K data s p ht (.localized h path i))
  exact lt_of_not_ge (fun hm => hn ⟨hv,hu,hm⟩)

theorem terminal_old_miss (path : Fin t → Fin 8) (i : Fin 8)
    (j : Fin (FirstHeight.depth (m+1)+2))
    (hv : Visible (TaskState.retired s) (oldNode path))
    (hu : ¬NodeDisclosed s (oldChild path i)) : |oldReadout data path i j p.point|≤1/8 := by
  have hn := of_decide_eq_false (terminal_trigger_false K data s p ht (.old path i j))
  exact le_of_not_gt (fun hm => hn ⟨hv,hu,hm⟩)

theorem terminal_inner_miss (leaf : Leaf (t+1)) (task : Fin (m+1))
    (j : Fin (Inner.absoluteDepth+2)) (hc : TaskState.current s=some leaf)
    (hu : ¬TaskDisclosed s leaf task) : |innerReadout data leaf task j p.point|≤1/8 := by
  have hn := of_decide_eq_false (terminal_trigger_false K data s p ht (.inner leaf task j))
  exact le_of_not_gt (fun hm => hn ⟨hc,hu,hm⟩)

theorem terminal_future_mark_miss (leaf : Leaf (t+1)) (task : Fin (m+1))
    (hc : TaskState.current s=some leaf) (hu : ¬MarkSupplied s leaf task) :
    |markReadout data leaf task p.point|≤1/3072 := by
  have hn := of_decide_eq_false (terminal_trigger_false K data s p ht (.futureMark leaf task))
  exact le_of_not_gt (fun hm => hn ⟨hc,hu,hm⟩)

omit ht K in
theorem current_mark_miss (leaf : Leaf (t+1)) (hc : TaskState.current s=some leaf)
    (hh : hit data s p.point=false) :
    |markReadout data leaf ⟨(s.completed leaf).val,TaskState.current_live s hc⟩ p.point|≤1/3072 := by
  rw [hit_current data s p.point hc] at hh
  exact le_of_not_gt (of_decide_eq_false hh)

end GradientHessian.GeometricRepair
