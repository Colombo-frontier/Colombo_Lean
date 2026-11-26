import SampleReuse.PersistentStageAgreement
import SampleReuse.PersistentHistoryEvents

/-! Response counts of the one-array stage simulator are charged to actual
original oracle calls. Repeated handles are still counted as calls. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type}

theorem persistentStageKey_selected (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start : ℕ) (s₀ : S)
    (n : ℕ) (h : FiniteHistory Unit (Fin d → SignedCoefficient R) n) :
    (persistentStageKey P Θ A β past j start s₀ n h).isSome = true ↔
      persistentStageIndex P Θ β j start n (persistentStageState P Θ A β past j start s₀ n h) = j.val := by
  unfold persistentStageKey
  dsimp only
  split_ifs <;> simp_all

def stageTableCount (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start : ℕ) (s₀ : S) : ℕ → ℕ
  | 0 => 0
  | n + 1 => stageTableCount P Θ A β table j start s₀ n +
    if persistentStageIndex P Θ β j start n (persistentStageTableRun P Θ A β table j start s₀ n) = j.val then 1 else 0

theorem persistentStage_response_count (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ Θ' : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start : ℕ) (s₀ : S)
    (a₀ : Fin d → SignedCoefficient R)
    (hΘ : ∀ i, i.val < j.val → Θ i = Θ' i)
    (hz : ∀ r i, i.val < j.val → past r i = table r i) : ∀ n,
    tableResponseCount (persistentStageKey P Θ A β past j start s₀) (fun r => r.isSome = true)
      () (targetArrayTable table j a₀) n = stageTableCount P Θ' A β table j start s₀ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tableResponseCount, stageTableCount, ih]
    congr 1
    rw [persistentStageKey_selected, persistentStageState_table_history P Θ Θ' A β past table j start s₀ a₀ hΘ hz]
    have he : persistentStageIndex P Θ β j start n (persistentStageTableRun P Θ' A β table j start s₀ n) =
        persistentStageIndex P Θ' β j start n (persistentStageTableRun P Θ' A β table j start s₀ n) :=
      firstOrderLimitedProgress_prefix Θ Θ' β _ j.val hΘ
    rw [he]
    by_cases hk : persistentStageIndex P Θ' β j start n (persistentStageTableRun P Θ' A β table j start s₀ n) = j.val
    · simp only [if_pos hk]
    · simp only [if_neg hk]

theorem persistentStageResponseCount_succ (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (stage n : ℕ) :
    persistentStageResponseCount P Θ A β table stage (n + 1) =
      persistentStageResponseCount P Θ A β table stage n +
        if persistentComparisonIndex P Θ A β table n = stage then 1 else 0 := by
  unfold persistentStageResponseCount
  rw [firstOrderStageResponseCount, persistentComparisonIndex_as_tape]

theorem persistentStageResponseCount_mono (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (stage : ℕ) :
    Monotone (persistentStageResponseCount P Θ A β table stage) :=
  firstOrderStageResponseCount_mono (persistentPointPolicy P) Θ A β _ stage

/-- Every simulator response before first activation is an actual response
with the same historical index. The entry time may itself be random. -/
theorem stageTableCount_le_original (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start : ℕ)
    (hp : (persistentComparisonRun P Θ A β table start).1 + 1 = j.val ∨
      (persistentComparisonRun P Θ A β table start).1 = j.val) :
    ∀ n, (∀ t, t < n → ¬0 < firstOrderBlockCompletion (Θ j)
      (firstOrderDilation d T β (persistentComparisonQuery P Θ A β table (start + t)).1 j)) →
      stageTableCount P Θ A β table j start (persistentComparisonRun P Θ A β table start).2 n ≤
        persistentStageResponseCount P Θ A β table j.val (start + n) := by
  intro n
  induction n with
  | zero => intro _; exact Nat.zero_le _
  | succ n ih =>
    intro hn
    have hh := ih (fun t ht => hn t (by omega))
    have hk := persistentStageIndex_before_activation P Θ A β table j start n hp (fun t ht => hn t (by omega))
    rw [stageTableCount, hk]
    change _ ≤ persistentStageResponseCount P Θ A β table j.val (start + n + 1)
    rw [persistentStageResponseCount_succ]
    exact Nat.add_le_add_right hh _

end
end SampleReuse
