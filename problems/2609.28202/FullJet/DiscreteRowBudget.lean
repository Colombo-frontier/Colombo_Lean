import FullJet.ParityGrid
import FullJet.ScaleParameters

namespace FullJet

/-- One fixed, conservative universal scale for the information estimate.
It also absorbs the genuinely observed free initialization row. -/
def rowBudgetDivisor : ℕ := 1048576

def largeSampleThreshold : ℕ := 2 * rowBudgetDivisor

theorem exists_discrete_row_budget (n : ℕ) (hn : largeSampleThreshold ≤ n) :
    ∃ m k q : ℕ, 0 < m ∧ m ≤ n ∧ 2 * k = n + m ∧
      Real.sqrt n ≤ m ∧ (m : ℝ) ≤ 2 * Real.sqrt n ∧
      8 * (m : ℝ) + 9 * (q + 1 : ℕ) ≤ n ∧
      (q + 1 : ℕ) * ((m : ℝ) / n) ^ 2 ≤ (5 / 32 : ℝ) ^ 2 / 1024 ∧
      (n : ℝ) / largeSampleThreshold ≤ (q + 1 : ℕ) := by
  have hn0 : 0 < n := by norm_num [largeSampleThreshold, rowBudgetDivisor] at hn; omega
  have hn1024 : 1024 ≤ n := by norm_num [largeSampleThreshold, rowBudgetDivisor] at hn; omega
  obtain ⟨m, hm, hmn16, hparity, hlow, hhigh⟩ := exists_parity_bias_sixteenth n hn1024
  let k := (n + m) / 2
  have hbalance : 2 * k = n + m := by dsimp [k]; omega
  let r := n / rowBudgetDivisor
  let q := r - 1
  have hr2 : 2 ≤ r := by
    exact (Nat.le_div_iff_mul_le (by norm_num [rowBudgetDivisor])).mpr hn
  have hqr : q + 1 = r := by omega
  have hrupper : (r : ℝ) ≤ (n : ℝ) / rowBudgetDivisor := by
    exact Nat.cast_div_le
  have hrlower : (n : ℝ) / largeSampleThreshold ≤ r := by
    have hrem := Nat.mod_lt n (show 0 < rowBudgetDivisor by norm_num [rowBudgetDivisor])
    have hsplit := Nat.mod_add_div n rowBudgetDivisor
    have hupper : n < rowBudgetDivisor * (r + 1) := by
      dsimp [r, rowBudgetDivisor] at hrem hsplit ⊢
      omega
    have hupper' : (n : ℝ) < (rowBudgetDivisor : ℝ) * (r + 1) := by exact_mod_cast hupper
    have hr2' : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    change (n : ℝ) / 2097152 ≤ (r : ℝ)
    change (n : ℝ) < 1048576 * ((r : ℝ) + 1) at hupper'
    linarith only [hupper', hr2']
  have hmn : m ≤ n := by
    have h : (m : ℝ) ≤ n := by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    exact_mod_cast h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hs := Real.sq_sqrt (Nat.cast_nonneg n)
  have hmsq : (m : ℝ) ^ 2 ≤ 4 * n := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hrho : ((m : ℝ) / n) ^ 2 ≤ 4 / n := by
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hn') hn').mpr
    have hprod := mul_le_mul_of_nonneg_right hmsq hn'.le
    nlinarith only [hprod]
  refine ⟨m, k, q, by omega, hmn, hbalance, hlow, hhigh, ?_, ?_, ?_⟩
  · rw [hqr]
    norm_num [rowBudgetDivisor] at hrupper
    linarith
  · rw [hqr]
    calc
      _ ≤ ((n : ℝ) / rowBudgetDivisor) * (4 / n) :=
        mul_le_mul hrupper hrho (sq_nonneg _) (by positivity)
      _ = (4 / (rowBudgetDivisor : ℝ)) * ((n : ℝ) / n) := by ring
      _ = 4 / (rowBudgetDivisor : ℝ) := by rw [div_self hn'.ne', mul_one]
      _ ≤ _ := by norm_num [rowBudgetDivisor]
  · simpa [hqr] using hrlower

end FullJet
