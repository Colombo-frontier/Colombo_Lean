import NoisyZO.RateArithmetic
import Mathlib.Tactic

/-!
# Converting stochastic-gradient iterations to raw oracle calls

One multiscale iteration uses a fixed positive number `q` of raw scalar
queries.  Integer division therefore gives `n = T / q` iterations.  Above
the threshold `T ≥ 2q`, this file proves the constant-factor comparison needed
to replace the iteration budget by the raw-query budget.
-/

namespace NoisyZO

/-- The scheduled iterations never exceed the raw call budget. -/
theorem scheduled_iterations_fit {T q : ℕ} :
    q * (T / q) ≤ T :=
  Nat.mul_div_le T q

/-- If at least two batches are affordable, integer division loses at most a
factor of two: `T ≤ 2 q floor(T/q)`. -/
theorem raw_budget_le_twice_scheduled {T q : ℕ}
    (hq : 0 < q) (hT : 2 * q ≤ T) :
    T ≤ 2 * q * (T / q) := by
  have hn2 : 2 ≤ T / q := (Nat.le_div_iff_mul_le hq).2 hT
  have hlt : T < q * (T / q + 1) := Nat.lt_mul_div_succ T hq
  have hbatch : q * (T / q + 1) ≤ 2 * q * (T / q) := by
    have hsucc : T / q + 1 ≤ 2 * (T / q) := by omega
    calc
      q * (T / q + 1) ≤ q * (2 * (T / q)) :=
        Nat.mul_le_mul_left q hsucc
      _ = 2 * q * (T / q) := by ring
  exact (Nat.le_of_lt hlt).trans hbatch

/-- Real-valued rate comparison after replacing `n = floor(T/q)` by the raw
budget `T`. -/
theorem dimension_ratio_scheduled_le
    {d T q : ℕ} (hq : 0 < q) (hT : 2 * q ≤ T) :
    (d : ℝ) ^ 2 / (T / q : ℕ) ≤
      2 * q * (d : ℝ) ^ 2 / T := by
  have hnNat : 0 < T / q :=
    lt_of_lt_of_le (by norm_num : 0 < 2) ((Nat.le_div_iff_mul_le hq).2 hT)
  have hn : 0 < ((T / q : ℕ) : ℝ) := by exact_mod_cast hnNat
  have hTR : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 2 * q) hT)
  have hbudgetR : (T : ℝ) ≤ 2 * q * (T / q : ℕ) := by
    exact_mod_cast raw_budget_le_twice_scheduled hq hT
  rw [div_le_iff₀ hn]
  have hd2 : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
  calc
    (d : ℝ) ^ 2 ≤
        (2 * q * (d : ℝ) ^ 2 * (T / q : ℕ)) / T := by
      rw [le_div_iff₀ hTR]
      nlinarith
    _ = 2 * q * (d : ℝ) ^ 2 / T * (T / q : ℕ) := by ring

end NoisyZO
