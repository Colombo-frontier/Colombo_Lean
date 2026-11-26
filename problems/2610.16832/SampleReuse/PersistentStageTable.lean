import SampleReuse.PersistentStageSimulator
import SampleReuse.PersistentTableHistory

/-! The concrete one-array stage simulator agrees pathwise with the full
immutable-table scalar oracle with its frontier restricted to past blocks. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type}

def persistentStageTableRun (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start : ℕ) (s₀ : S) : ℕ → S
  | 0 => s₀
  | n + 1 => let s := persistentStageTableRun P Θ A β table j start s₀ n
    let q := P.query (start + n) s
    P.update (start + n) s (scaledFirstOrderTruncatedReply Θ A β (table q.2)
      (persistentStageIndex P Θ β j start n s) q.1)

def targetArrayTable {R : ℝ} (table : Handle → FirstOrderCoefficients d T R)
    (j : Fin (T + 1)) (a₀ : Fin d → SignedCoefficient R) : Option Handle → Fin d → SignedCoefficient R
  | none => a₀
  | some r => table r j

theorem persistentStageStep_key_reply (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ Θ' : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start : ℕ) (s₀ : S)
    (a₀ : Fin d → SignedCoefficient R)
    (hΘ : ∀ i, i.val < j.val → Θ i = Θ' i)
    (hz : ∀ r i, i.val < j.val → past r i = table r i)
    (n : ℕ) (h : FiniteHistory Unit (Fin d → SignedCoefficient R) n) :
    let s := persistentStageState P Θ A β past j start s₀ n h
    persistentStageStep P Θ A β past j start n s
      (targetArrayTable table j a₀ (persistentStageKey P Θ A β past j start s₀ n h)) =
      P.update (start + n) s (scaledFirstOrderTruncatedReply Θ' A β (table (P.query (start + n) s).2)
        (persistentStageIndex P Θ' β j start n s) (P.query (start + n) s).1) := by
  dsimp only
  let s := persistentStageState P Θ A β past j start s₀ n h
  change persistentStageStep P Θ A β past j start n s
    (targetArrayTable table j a₀ (if persistentStageIndex P Θ β j start n s = j.val
      then some (P.query (start + n) s).2 else none)) = _
  by_cases hk : persistentStageIndex P Θ β j start n s = j.val
  · simp only [if_pos hk, targetArrayTable]
    exact persistentStageStep_full_reply P Θ Θ' A β past table j start n s hΘ hz
  · have hlt : persistentStageIndex P Θ β j start n s < j.val :=
      lt_of_le_of_ne (firstOrderLimitedProgress_le Θ β _ _).2 hk
    have he := persistentStageStep_array_irrelevant P Θ A β past j start n s a₀
      (table (P.query (start + n) s).2 j) hlt
    have hf := he.trans (persistentStageStep_full_reply P Θ Θ' A β past table j start n s hΘ hz)
    simpa only [if_neg hk, targetArrayTable] using hf

/-- Supplying a saved target array on repeated handle requests produces
exactly the same numerical scalar jets as the full restricted sample loss. -/
theorem persistentStageState_table_history (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ Θ' : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (past table : Handle → FirstOrderCoefficients d T R) (j : Fin (T + 1)) (start : ℕ) (s₀ : S)
    (a₀ : Fin d → SignedCoefficient R)
    (hΘ : ∀ i, i.val < j.val → Θ i = Θ' i)
    (hz : ∀ r i, i.val < j.val → past r i = table r i) : ∀ n,
    persistentStageState P Θ A β past j start s₀ n
      (tableHistory (persistentStageKey P Θ A β past j start s₀) () (targetArrayTable table j a₀) n) =
      persistentStageTableRun P Θ' A β table j start s₀ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change persistentStageStep P Θ A β past j start n
      (persistentStageState P Θ A β past j start s₀ n
        (tableHistory (persistentStageKey P Θ A β past j start s₀) () (targetArrayTable table j a₀) n))
      (targetArrayTable table j a₀ (persistentStageKey P Θ A β past j start s₀ n
        (tableHistory (persistentStageKey P Θ A β past j start s₀) () (targetArrayTable table j a₀) n))) = _
    rw [persistentStageStep_key_reply P Θ Θ' A β past table j start s₀ a₀ hΘ hz, ih]
    rfl

end
end SampleReuse
