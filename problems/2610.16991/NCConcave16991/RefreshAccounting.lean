import NCConcave16991.UpperRecurrence

/-! # Literal chronological query counts of the persistent algorithm -/

open scoped BigOperators

namespace NCConcave16991

theorem sum_refresh_cost (n q S : ℕ) :
    (∑ t ∈ Finset.range S, if (t + 1) % q = 0 then n else 0) = n * (S / q) := by
  induction S with
  | zero => simp
  | succ S ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : (S + 1) % q = 0
    · rw [ite_eq_left h, Nat.succ_div_of_mod_eq_zero h]
      ring
    · rw [ite_eq_right h, Nat.succ_div_of_mod_ne_zero h]
      simp

/-- Initial full pass, followed by exactly the public inner and anchor-update
calls at each center. Refresh positions are determined before the oracle. -/
def persistentChronologicalBudget (n q b k S : ℕ) : ℕ :=
  n + ∑ t ∈ Finset.range S, (2 * k + if (t + 1) % q = 0 then n else 2 * b)

theorem persistentChronologicalBudget_le (n q b k S : ℕ) (hq : 0 < q) :
    persistentChronologicalBudget n q b k S ≤ persistentQueryBudget n q b k S := by
  have hpoint (t : ℕ) :
      (2 * k + if (t + 1) % q = 0 then n else 2 * b) ≤
        2 * k + (if (t + 1) % q = 0 then n else 0) + 2 * b := by
    split <;> omega
  have hs := Finset.sum_le_sum (s := Finset.range S) (fun t _ ↦ hpoint t)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, sum_refresh_cost] at hs
  have hceil : S / q ≤ (S + q - 1) / q := Nat.div_le_div_right (by omega)
  have hn := Nat.mul_le_mul_left n hceil
  dsimp [persistentChronologicalBudget, persistentQueryBudget]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  nlinarith only [hs, hn]

end NCConcave16991
