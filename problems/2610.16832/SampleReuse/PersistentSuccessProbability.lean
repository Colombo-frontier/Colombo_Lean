import SampleReuse.PersistentCompletionProbability
import SecondOrder.FirstOrderHorizonConstants

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {H S : Type}

def persistentOriginalOutput (P : PersistentFirstOrderPolicy d T H S)
    (Θ : Fin (T+1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : H → FirstOrderCoefficients d T R) (N : ℕ) : Point (FirstOrderDimension d T) :=
  (P.query N (persistentRichRun P Θ A β table N)).1

theorem persistent_success_transfer (P : PersistentFirstOrderPolicy d T H S)
    (Θ : Fin (T+1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : H → FirstOrderCoefficients d T R) (N : ℕ)
    (success : Point (FirstOrderDimension d T) → Prop)
    (hcomplete : ∀ x, success x → firstOrderProgress Θ (firstOrderDilation d T β x) = T+1)
    (hs : success (persistentOriginalOutput P Θ A β table N))
    (hfar : persistentNoFarJump P Θ A β table (N+1)) :
    persistentOutputProgress P Θ A β table N = T+1 := by
  have hc := persistentComparison_coupling P Θ A β table N (fun n hn => hfar n (by omega))
  have hs' : success (persistentComparisonQuery P Θ A β table N).1 := by
    simpa only [persistentOriginalOutput,hc,persistentComparisonQuery] using hs
  have hi : persistentComparisonIndex P Θ A β table N = T+1 := by
    unfold persistentComparisonIndex
    rw [firstOrderLimitedProgress_no_far Θ β _ _ (hfar N (by omega))]
    exact hcomplete _ hs'
  have hle := firstOrderComparisonRun_progress_le (persistentPointPolicy P) Θ A β
    (persistentComparisonTape P Θ A β table) N
  rw [← persistentComparisonRun_as_tape] at hle
  simp only [persistentOutputProgress,hi,max_eq_right hle]

variable [Fintype H]

theorem persistent_original_success_probability (P : PersistentFirstOrderPolicy d T H S)
    (A β R : ℝ) (hR : 2 ≤ R) (N : ℕ)
    (success : (Fin (T+1) → Fin d → Bool) → Point (FirstOrderDimension d T) → Prop)
    (hcomplete : ∀ Θ x, success Θ x → firstOrderProgress Θ (firstOrderDilation d T β x) = T+1) :
    pmfEventProbability (persistentSourceLaw d T H R hR) (fun w => decide
      (success (persistentSourceHidden w)
        (persistentOriginalOutput P (persistentSourceHidden w) A β (persistentSourceTable w) N))) ≤
    pmfEventProbability (persistentSourceLaw d T H R hR) (fun w => decide
      (persistentOutputProgress P (persistentSourceHidden w) A β (persistentSourceTable w) N = T+1)) +
      (N+1:ℕ)*(T+1:ℕ)*(2*Real.exp (-(d:ℝ)/128)) := by
  have hp (w : Fin (T+1) → PersistentBlock d H R) :
      (if success (persistentSourceHidden w)
        (persistentOriginalOutput P (persistentSourceHidden w) A β (persistentSourceTable w) N)
        then (1:ℝ) else 0) ≤
      (if persistentOutputProgress P (persistentSourceHidden w) A β (persistentSourceTable w) N = T+1
        then (1:ℝ) else 0) +
      (if ∃ n : Fin (N+1), ∃ j : Fin (T+1), persistentFarCoordinate P A β j n.val w
        then (1:ℝ) else 0) := by
    by_cases hs : success (persistentSourceHidden w)
      (persistentOriginalOutput P (persistentSourceHidden w) A β (persistentSourceTable w) N)
    · rw [if_pos hs]
      by_cases hf : ∃ n : Fin (N+1), ∃ j : Fin (T+1), persistentFarCoordinate P A β j n.val w
      · rw [if_pos hf]; split_ifs <;> norm_num
      · have hn : persistentNoFarJump P (persistentSourceHidden w) A β (persistentSourceTable w) (N+1) := by
          intro n hn j hj ha
          exact hf ⟨⟨n,hn⟩,j,hj,ha⟩
        rw [if_pos (persistent_success_transfer P _ A β _ N _ (hcomplete _) hs hn),if_neg hf]
        norm_num
    · rw [if_neg hs]; split_ifs <;> norm_num
  simp only [pmfEventProbability_mean,decide_eq_true_eq]
  apply (pmfMean_mono _ hp).trans
  rw [pmfMean_add]
  have hf := persistent_far_union_bound P A β R hR N
  simp only [pmfEventProbability_mean,decide_eq_true_eq] at hf
  exact add_le_add_left hf _

theorem persistent_original_success_one_eighth (P : PersistentFirstOrderPolicy d T H S)
    (hT : 0 < T) (A β R : ℝ) (hR : 2 ≤ R) (cap N : ℕ) (hcap0 : 0 < cap)
    (hbudget : 2*N ≤ T*cap)
    (hfast : ∀ i : Fin T,
      pmfEventProbability (persistentSourceLaw d T H R hR) (fun w => decide
        (persistentStageReached P (persistentSourceHidden w) A β (persistentSourceTable w) i.succ N ∧
          persistentStageResponseCount P (persistentSourceHidden w) A β
            (persistentSourceTable w) (i.val+1) N < cap)) ≤ 1/32)
    (hfar : 128*Real.log (32*(N+1:ℕ)*(T+1:ℕ)) ≤ (d:ℝ))
    (success : (Fin (T+1) → Fin d → Bool) → Point (FirstOrderDimension d T) → Prop)
    (hcomplete : ∀ Θ x, success Θ x → firstOrderProgress Θ (firstOrderDilation d T β x) = T+1) :
    pmfEventProbability (persistentSourceLaw d T H R hR) (fun w => decide
      (success (persistentSourceHidden w)
        (persistentOriginalOutput P (persistentSourceHidden w) A β (persistentSourceTable w) N))) ≤
      1/8 := by
  have hs := persistent_original_success_probability P A β R hR N success hcomplete
  have hc := persistent_completion_probability P hT A β R hR cap N hcap0 hbudget hfast
  have hf := firstOrderFarHorizon_small N T hfar
  simp only [← mul_assoc] at hf
  linarith only [hs,hc,hf]

/-- The source-package law is exactly the hidden prior followed by immutable
iid full-loss samples; this equality does not refresh samples on revisits. -/
theorem persistent_original_success_law (P : PersistentFirstOrderPolicy d T H S)
    (A β R : ℝ) (hR : 2 ≤ R) (N : ℕ)
    (success : (Fin (T+1) → Fin d → Bool) → Point (FirstOrderDimension d T) → Prop) :
    pmfEventProbability (persistentOriginalJointLaw d T H R hR) (fun w => decide
      (success w.1 (persistentOriginalOutput P w.1 A β w.2 N))) =
    pmfEventProbability (persistentSourceLaw d T H R hR) (fun w => decide
      (success (persistentSourceHidden w)
        (persistentOriginalOutput P (persistentSourceHidden w) A β (persistentSourceTable w) N))) := by
  rw [← persistent_source_eq_original (Handle := H) R hR]
  simp only [pmfEventProbability_mean,pmfMean_map]
  rfl

end
end SampleReuse
