import SampleReuse.PersistentStageEntry
import SecondOrder.FirstOrderStageCompletion

/-! Reuse of deterministic comparison/counting identities only. The
coefficient tape below is generated from immutable handles along the actual
adaptive comparison path; no fresh-response probability law is imported
as a probability law for this tape. -/

open SecondOrder
open scoped Classical BigOperators
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type*}

def persistentPointPolicy (P : PersistentFirstOrderPolicy d T Handle S) : FirstOrderPolicy d T S where
  initial := P.initial
  query n s := (P.query n s).1
  update := P.update

def persistentComparisonTape (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (n : ℕ) : FirstOrderCoefficients d T R :=
  table (persistentComparisonQuery P Θ A β table n).2

theorem persistentComparisonRun_as_tape (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) : ∀ n,
    persistentComparisonRun P Θ A β table n =
      firstOrderComparisonRun (persistentPointPolicy P) Θ A β (persistentComparisonTape P Θ A β table) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change persistentComparisonStep P Θ A β table n (persistentComparisonRun P Θ A β table n) =
      firstOrderComparisonStep (persistentPointPolicy P) Θ A β n
        (firstOrderComparisonRun (persistentPointPolicy P) Θ A β (persistentComparisonTape P Θ A β table) n)
        (persistentComparisonTape P Θ A β table n)
    rw [← ih]
    rfl

theorem persistentComparisonIndex_as_tape (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (n : ℕ) :
    persistentComparisonIndex P Θ A β table n =
      firstOrderComparisonIndex (persistentPointPolicy P) Θ A β (persistentComparisonTape P Θ A β table) n := by
  unfold persistentComparisonIndex firstOrderComparisonIndex persistentComparisonQuery firstOrderComparisonQuery
  rw [persistentComparisonRun_as_tape]
  rfl

theorem persistentStageEntry_as_tape (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (stage n : ℕ) :
    persistentStageEntry P Θ A β table stage n ↔
      firstOrderStageEntry (persistentPointPolicy P) Θ A β (persistentComparisonTape P Θ A β table) stage n := by
  simp only [persistentStageEntry, firstOrderStageEntry, persistentComparisonRun_as_tape,
    persistentComparisonIndex_as_tape]

def persistentStageResponseCount (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (stage N : ℕ) : ℕ :=
  firstOrderStageResponseCount (persistentPointPolicy P) Θ A β
    (persistentComparisonTape P Θ A β table) stage N

/-- The output test at N is uncharged; each actual response contributes
to at most one of the positive target stages. -/
theorem persistentStageResponseCount_budget (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (N : ℕ) :
    (∑ i : Fin T, persistentStageResponseCount P Θ A β table (i.val + 1) N) ≤ N :=
  firstOrderStageResponseCount_budget (persistentPointPolicy P) Θ A β _ N

theorem persistentStageEntry_exists_before (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (stage : ℕ) (hs : 0 < stage) (N : ℕ)
    (hh : stage ≤ (persistentComparisonRun P Θ A β table N).1) :
    ∃ n, n < N ∧ persistentStageEntry P Θ A β table stage n := by
  rw [persistentComparisonRun_as_tape] at hh
  obtain ⟨n, hn, he⟩ := firstOrderStageEntry_exists_before (persistentPointPolicy P) Θ A β _ stage hs N hh
  exact ⟨n, hn, (persistentStageEntry_as_tape P Θ A β table stage n).mpr he⟩

end
end SampleReuse
