import SampleReuse.PersistentEntryPrior

/-! Entry-conditioned continuation expectations are computed by resampling
the entire target sign/table package from its original joint law. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type} [Fintype Handle]

theorem persistent_entry_resample_mean (P : PersistentFirstOrderPolicy d T Handle S)
    (A β R : ℝ) (hR : 2 ≤ R) (j : Fin (T + 1)) (n : ℕ)
    (E : S → (Point (FirstOrderDimension d T) × Handle) → Prop)
    (F : (Fin (T + 1) → PersistentBlock d Handle R) → ℝ) :
    pmfMean (persistentSourceLaw d T Handle R hR)
      (fun w => if persistentEntrySlice P A β j n E w then F w else 0) =
      pmfMean (persistentSourceLaw d T Handle R hR) (fun w =>
        if persistentEntrySlice P A β j n E w then
          pmfMean (persistentBlockLaw d Handle R hR) (fun b => F (Function.update w j b)) else 0) := by
  unfold persistentSourceLaw
  rw [← finitePiPMF_resample_mean _ j]
  apply pmfMean_congr
  intro w
  by_cases he : persistentEntrySlice P A β j n E w
  · simp only [if_pos he]
    apply pmfMean_congr
    intro b
    rw [if_pos ((persistentEntrySlice_update P A β j n E w b).mp he)]
  · simp only [if_neg he]
    have hh : (fun b : PersistentBlock d Handle R =>
        if persistentEntrySlice P A β j n E (Function.update w j b) then F (Function.update w j b) else 0) =
        fun _ => 0 := by
      funext b
      rw [if_neg ((persistentEntrySlice_update P A β j n E w b).not.mp he)]
    rw [hh, pmfMean_const]

theorem persistent_entry_probability_bound (P : PersistentFirstOrderPolicy d T Handle S)
    (A β R : ℝ) (hR : 2 ≤ R) (j : Fin (T + 1)) (n : ℕ)
    (E : S → (Point (FirstOrderDimension d T) × Handle) → Prop)
    (F : (Fin (T + 1) → PersistentBlock d Handle R) → Prop) {q : ℝ}
    (hb : ∀ w, persistentEntrySlice P A β j n E w →
      pmfEventProbability (persistentBlockLaw d Handle R hR) (fun b => decide (F (Function.update w j b))) ≤ q) :
    pmfEventProbability (persistentSourceLaw d T Handle R hR)
      (fun w => decide (persistentEntrySlice P A β j n E w ∧ F w)) ≤
      q * pmfEventProbability (persistentSourceLaw d T Handle R hR)
        (fun w => decide (persistentEntrySlice P A β j n E w)) := by
  rw [pmfEventProbability_mean]
  simp only [decide_eq_true_eq, ite_and]
  rw [persistent_entry_resample_mean P A β R hR j n E (fun w => if F w then 1 else 0),
    pmfEventProbability_mean, ← pmfMean_mul]
  apply pmfMean_mono
  intro w
  by_cases he : persistentEntrySlice P A β j n E w
  · simp only [if_pos he, decide_eq_true_eq, mul_one]
    simpa only [pmfEventProbability_mean, decide_eq_true_eq] using hb w he
  · simp only [if_neg he, decide_eq_true_eq, mul_zero, le_refl]

end
end SampleReuse
