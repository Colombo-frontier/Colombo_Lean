import NCConcave16991.OracleProgramFold
import NCConcave16991.RefreshAccounting

/-! # Exact accounting of variable-cost interactive program folds -/

open scoped BigOperators

namespace NCConcave16991.OracleProgram

theorem foldBudget_eq_sum (cost : ℕ → ℕ) (k t : ℕ) :
    foldBudget cost k t = ∑ i ∈ Finset.range k, cost (t + i) := by
  induction k generalizing t with
  | zero => simp [foldBudget]
  | succ k ih =>
    rw [foldBudget, ih]
    rw [show k + 1 = 1 + k by omega, Finset.sum_range_add]
    simp only [Finset.sum_range_one, Nat.add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega

theorem foldBudget_zero_eq_sum (cost : ℕ → ℕ) (k : ℕ) :
    foldBudget cost k 0 = ∑ t ∈ Finset.range k, cost t := by
  simpa only [Nat.zero_add] using foldBudget_eq_sum cost k 0

theorem foldBudget_mono_length (cost : ℕ → ℕ) {k K : ℕ} (h : k ≤ K) (t : ℕ) :
    foldBudget cost k t ≤ foldBudget cost K t := by
  rw [foldBudget_eq_sum, foldBudget_eq_sum]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem persistent_program_budget (n q b k S : ℕ) (hq : 0 < q) :
    n + foldBudget (fun t ↦ 2 * k + if (t + 1) % q = 0 then n else 2 * b) S 0 ≤
      persistentQueryBudget n q b k S := by
  rw [foldBudget_zero_eq_sum]
  exact persistentChronologicalBudget_le n q b k S hq

end NCConcave16991.OracleProgram
