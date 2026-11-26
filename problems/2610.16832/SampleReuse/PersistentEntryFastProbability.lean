import SampleReuse.PersistentStageSource
import SampleReuse.PersistentReachedTransfer
import SampleReuse.PersistentEntryResampling

/-! Uniform fast-stage probability at each actual entrance. The probability
of that entrance is retained multiplicatively, avoiding a horizon factor. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type}

def persistentFastOutcome (P : PersistentFirstOrderPolicy d T Handle S) (A β : ℝ) {R : ℝ}
    (j : Fin (T + 1)) (cap N : ℕ) (w : Fin (T + 1) → PersistentBlock d Handle R) : Prop :=
  firstOrderStageReached (persistentPointPolicy P) (persistentSourceHidden w) A β
    (persistentComparisonTape P (persistentSourceHidden w) A β (persistentSourceTable w)) j N ∧
  persistentStageResponseCount P (persistentSourceHidden w) A β (persistentSourceTable w) j.val N < cap

theorem persistent_resampled_fast_marked (P : PersistentFirstOrderPolicy d T Handle S)
    (A β : ℝ) {R : ℝ} (j : Fin (T + 1)) (start N cap : ℕ) (a₀ : Fin d → SignedCoefficient R)
    (w : Fin (T + 1) → PersistentBlock d Handle R)
    (he : persistentStageEntry P (persistentSourceHidden w) A β (persistentSourceTable w) j.val start)
    (b : PersistentBlock d Handle R) (hf : persistentFastOutcome P A β j cap N (Function.update w j b)) :
    let s₀ := (persistentSourceRun P A β w start).2
    let query := persistentStageKey P (persistentSourceHidden w) A β (persistentSourceTable w) j start s₀
    let points := persistentStagePoint P (persistentSourceHidden w) A β (persistentSourceTable w) j start s₀
    tableHistory (liftPublicQuery query) (b.1, ()) (extendOptionTable a₀ b.2) N ∈
      signTableFastSet query (fun r => r.isSome = true) cap points N := by
  have hΘ : ∀ i, i.val < j.val → persistentSourceHidden w i = persistentSourceHidden (Function.update w j b) i :=
    fun i hi => congrArg Prod.fst (persistentSource_update_prefix w j b i hi)
  have hz : ∀ r i, i.val < j.val →
      persistentSourceTable w r i = persistentSourceTable (Function.update w j b) r i :=
    fun r i hi => congrArg (fun a : PersistentBlock d Handle R => a.2 r) (persistentSource_update_prefix w j b i hi)
  have hh := persistentStageEntry_prefix P _ _ A β _ _ j.val start hΘ hz he
  have hm := persistent_reached_fast_marked P (persistentSourceHidden w)
    (persistentSourceHidden (Function.update w j b)) A β (persistentSourceTable w)
    (persistentSourceTable (Function.update w j b)) j start N cap a₀ hΘ hz hh.1 hf.1 hf.2
  dsimp only at hm ⊢
  rw [← hh.2.1] at hm
  have hsign : persistentSourceHidden (Function.update w j b) j = b.1 := by
    simp only [persistentSourceHidden, Function.update_self]
  have htable : targetArrayTable (persistentSourceTable (Function.update w j b)) j a₀ =
      extendOptionTable a₀ b.2 := by
    funext r
    cases r <;> simp only [targetArrayTable, extendOptionTable, persistentSourceTable, Function.update_self]
  rw [hsign, htable] at hm
  exact hm

variable [Fintype Handle]

theorem persistent_entry_fast_probability (P : PersistentFirstOrderPolicy d T Handle S)
    (A β R : ℝ) (hR : 2 ≤ R) (j : Fin (T + 1)) (start N cap : ℕ) (a₀ : Fin d → SignedCoefficient R)
    {L : ℝ} (hL : 0 < L)
    (hlog : L ≤ Real.log (1 / ((N + 1 : ℕ) * (2 * Real.exp (-(d : ℝ) / 128)))))
    (hbudget : 32 * ((cap : ℝ) * ((d : ℝ) / R ^ 2) + Real.log 2) ≤ L) :
    pmfEventProbability (persistentSourceLaw d T Handle R hR)
      (fun w => decide (persistentEntrySlice P A β j start (fun _ _ => True) w ∧
        persistentFastOutcome P A β j cap N w)) ≤
      (1 / 32) * pmfEventProbability (persistentSourceLaw d T Handle R hR)
        (fun w => decide (persistentEntrySlice P A β j start (fun _ _ => True) w)) := by
  apply persistent_entry_probability_bound P A β R hR j start (fun _ _ => True)
    (persistentFastOutcome P A β j cap N)
  intro w hw
  let s₀ := (persistentSourceRun P A β w start).2
  let query := persistentStageKey P (persistentSourceHidden w) A β (persistentSourceTable w) j start s₀
  let points := persistentStagePoint P (persistentSourceHidden w) A β (persistentSourceTable w) j start s₀
  have hb := persistent_stage_source_fast_bound R hR query a₀ cap N points hL hlog hbudget
  apply le_trans _ hb
  rw [pmfEventProbability_mean, pmfEventProbability_mean]
  apply pmfMean_mono
  intro b
  have ht := persistent_resampled_fast_marked P A β j start N cap a₀ w hw.1 b
  simp only [decide_eq_true_eq]
  split_ifs with hf hm <;> try norm_num
  exact False.elim (hm (ht hf))

end
end SampleReuse
