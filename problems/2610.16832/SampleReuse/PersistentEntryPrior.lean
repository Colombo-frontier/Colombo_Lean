import SampleReuse.PersistentSourceLaw

/-! Entry-prior factorization under the actual joint law of hidden signs
and reusable coefficient tables. No conditional law is postulated. -/

open SecondOrder
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type} [Fintype Handle]

def persistentEntrySlice (P : PersistentFirstOrderPolicy d T Handle S) (A β : ℝ) {R : ℝ}
    (j : Fin (T + 1)) (n : ℕ)
    (E : S → (Point (FirstOrderDimension d T) × Handle) → Prop)
    (w : Fin (T + 1) → PersistentBlock d Handle R) : Prop :=
  persistentStageEntry P (persistentSourceHidden w) A β (persistentSourceTable w) j.val n ∧
    E (persistentSourceRun P A β w n).2 (persistentSourceQuery P A β w n)

omit [Fintype Handle] in
theorem persistentEntrySlice_update (P : PersistentFirstOrderPolicy d T Handle S) (A β : ℝ) {R : ℝ}
    (j : Fin (T + 1)) (n : ℕ)
    (E : S → (Point (FirstOrderDimension d T) × Handle) → Prop)
    (w : Fin (T + 1) → PersistentBlock d Handle R) (b : PersistentBlock d Handle R) :
    persistentEntrySlice P A β j n E w ↔ persistentEntrySlice P A β j n E (Function.update w j b) := by
  have hΘ : ∀ i, i.val < j.val →
      persistentSourceHidden w i = persistentSourceHidden (Function.update w j b) i :=
    fun i hi => congrArg Prod.fst (persistentSource_update_prefix w j b i hi)
  have hz : ∀ r i, i.val < j.val →
      persistentSourceTable w r i = persistentSourceTable (Function.update w j b) r i :=
    fun r i hi => congrArg (fun a : PersistentBlock d Handle R => a.2 r)
      (persistentSource_update_prefix w j b i hi)
  constructor
  · intro he
    have hh := persistentStageEntry_prefix P _ _ A β _ _ j.val n hΘ hz he.1
    refine ⟨hh.1, ?_⟩
    change E (persistentComparisonRun P _ A β _ n).2 (persistentComparisonQuery P _ A β _ n)
    rw [← hh.2.1, ← hh.2.2]
    exact he.2
  · intro he
    have hh := persistentStageEntry_prefix P _ _ A β _ _ j.val n
      (fun i hi => (hΘ i hi).symm) (fun r i hi => (hz r i hi).symm) he.1
    refine ⟨hh.1, ?_⟩
    change E (persistentComparisonRun P _ A β _ n).2 (persistentComparisonQuery P _ A β _ n)
    rw [← hh.2.1, ← hh.2.2]
    exact he.2

/-- Restricting to any specified entry state and query preserves the fresh
hidden sign prior. The equality is unnormalised and includes zero-mass
entry events. It resamples the sign and all its handle arrays jointly. -/
theorem persistent_entry_hidden_factor (P : PersistentFirstOrderPolicy d T Handle S)
    (A β R : ℝ) (hR : 2 ≤ R) (j : Fin (T + 1)) (n : ℕ)
    (E : S → (Point (FirstOrderDimension d T) × Handle) → Prop)
    (F : (Fin d → Bool) → ℝ) :
    pmfMean (persistentSourceLaw d T Handle R hR)
      (fun w => if persistentEntrySlice P A β j n E w then F (w j).1 else 0) =
      pmfMean (PMF.uniformOfFintype (Fin d → Bool)) F *
        pmfEventProbability (persistentSourceLaw d T Handle R hR)
          (fun w => decide (persistentEntrySlice P A β j n E w)) := by
  unfold persistentSourceLaw
  rw [← finitePiPMF_resample_mean _ j]
  rw [pmfEventProbability_mean, ← pmfMean_mul]
  apply pmfMean_congr
  intro w
  have he : (fun b : PersistentBlock d Handle R =>
      if persistentEntrySlice P A β j n E (Function.update w j b) then F ((Function.update w j b) j).1 else 0) =
      (fun b => if persistentEntrySlice P A β j n E w then F b.1 else 0) := by
    funext b
    simp only [← persistentEntrySlice_update P A β j n E w b, Function.update_self]
  rw [he]
  by_cases hh : persistentEntrySlice P A β j n E w
  · simp only [if_pos hh, decide_eq_true_eq, mul_one]
    exact persistentBlockLaw_hidden_mean R hR F
  · simp only [if_neg hh, pmfMean_const, decide_eq_true_eq, mul_zero]

end
end SampleReuse
