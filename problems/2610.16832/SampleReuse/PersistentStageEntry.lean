import SampleReuse.PersistentComparison

/-! Pointwise entry-prefix invariance, including immutable coefficients of
every handle. The target block and its full table can both be replaced. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type*}

def persistentStageEntry (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (stage n : ℕ) : Prop :=
  (persistentComparisonRun P Θ A β table n).1 < stage ∧
    persistentComparisonIndex P Θ A β table n = stage

theorem persistentStageEntry_progress (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) {stage n : ℕ}
    (he : persistentStageEntry P Θ A β table stage n) :
    (persistentComparisonRun P Θ A β table n).1 + 1 = stage := by
  have hi : persistentComparisonIndex P Θ A β table n ≤
      (persistentComparisonRun P Θ A β table n).1 + 1 := (firstOrderLimitedProgress_le Θ β _ _).2
  have h1 := he.1
  have h2 := he.2
  omega

theorem persistentStageEntry_no_previous (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) {stage n : ℕ}
    (he : persistentStageEntry P Θ A β table stage n) :
    ∀ t, t < n → persistentComparisonIndex P Θ A β table t < stage := by
  intro t ht
  have h1 := persistentComparison_index_le_next P Θ A β table t
  have h2 : (persistentComparisonRun P Θ A β table (t + 1)).1 ≤
      (persistentComparisonRun P Θ A β table n).1 := persistentComparison_progress_mono P Θ A β table (by omega)
  exact lt_of_le_of_lt (h1.trans h2) he.1

theorem persistentStageEntry_unique (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) {stage n k : ℕ}
    (hn : persistentStageEntry P Θ A β table stage n)
    (hk : persistentStageEntry P Θ A β table stage k) : n = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hh := persistentStageEntry_no_previous P Θ A β table hk n h
    rw [hn.2] at hh
    exact Nat.lt_irrefl _ hh
  · have hh := persistentStageEntry_no_previous P Θ A β table hn k h
    rw [hk.2] at hh
    exact Nat.lt_irrefl _ hh

/-- Before the first target-stage reply, the entry event, whole policy
state, and chosen handle/point ignore all target and future coefficients
and hidden vectors. Stage zero instead starts at the initial seed. -/
theorem persistentStageEntry_prefix (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ Θ' : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table table' : Handle → FirstOrderCoefficients d T R) (stage n : ℕ)
    (hΘ : ∀ i, i.val < stage → Θ i = Θ' i)
    (hz : ∀ r i, i.val < stage → table r i = table' r i)
    (he : persistentStageEntry P Θ A β table stage n) :
    persistentStageEntry P Θ' A β table' stage n ∧
      persistentComparisonRun P Θ A β table n = persistentComparisonRun P Θ' A β table' n ∧
      persistentComparisonQuery P Θ A β table n = persistentComparisonQuery P Θ' A β table' n := by
  have hp := persistentStageEntry_progress P Θ A β table he
  have hprefix : ∀ i, i.val < (persistentComparisonRun P Θ A β table n).1 + 1 → Θ i = Θ' i :=
    fun i hi => hΘ i (by omega)
  have hs := persistentComparison_prefix P Θ A β table n Θ' table' hprefix (fun r i hi => hz r i (by omega))
  have hq : persistentComparisonQuery P Θ A β table n = persistentComparisonQuery P Θ' A β table' n := by
    unfold persistentComparisonQuery
    rw [hs]
  have hi : persistentComparisonIndex P Θ A β table n = persistentComparisonIndex P Θ' A β table' n := by
    unfold persistentComparisonIndex
    rw [← hs, ← hq]
    exact firstOrderLimitedProgress_prefix Θ Θ' β _ _ hprefix
  refine ⟨⟨?_, ?_⟩, hs, hq⟩
  · rw [← hs]
    exact he.1
  · rw [← hi]
    exact he.2

theorem persistentStageEntry_iff_prefix (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ Θ' : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table table' : Handle → FirstOrderCoefficients d T R) (stage n : ℕ)
    (hΘ : ∀ i, i.val < stage → Θ i = Θ' i)
    (hz : ∀ r i, i.val < stage → table r i = table' r i) :
    persistentStageEntry P Θ A β table stage n ↔ persistentStageEntry P Θ' A β table' stage n :=
  ⟨fun he => (persistentStageEntry_prefix P Θ Θ' A β table table' stage n hΘ hz he).1,
    fun he => (persistentStageEntry_prefix P Θ' Θ A β table' table stage n
      (fun i hi => (hΘ i hi).symm) (fun r i hi => (hz r i hi).symm) he).1⟩

/-- A far hidden block and all its handles' coefficients can be resampled
jointly without altering the pre-response state or chosen query. -/
theorem persistentComparison_unrevealed_update (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (n : ℕ) (j : Fin (T + 1))
    (hj : (persistentComparisonRun P Θ A β table n).1 + 1 ≤ j.val)
    (θ : Fin d → Bool) (z : Handle → Fin d → SignedCoefficient R) :
    persistentComparisonRun P Θ A β table n =
      persistentComparisonRun P (Function.update Θ j θ) A β
        (fun r => Function.update (table r) j (z r)) n := by
  apply persistentComparison_prefix
  · intro i hi
    exact (Function.update_of_ne (by intro he; subst i; omega) _ _).symm
  · intro r i hi
    exact (Function.update_of_ne (by intro he; subst i; omega) _ _).symm

end
end SampleReuse
