import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace FullJet

/-- Explicit admissible parity-compatible bias numerator, close to `√n`. -/
theorem exists_parity_bias (n : ℕ) (hn : 1024 ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n / 8 ∧ m % 2 = n % 2 ∧
      Real.sqrt n ≤ m ∧ (m : ℝ) ≤ 2 * Real.sqrt n := by
  let t : ℝ := Real.sqrt n
  let m : ℕ := 2 * ⌈t / 2⌉₊ + n % 2
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hnreal : (1024 : ℝ) ≤ n := by exact_mod_cast hn
  have ht32 : 32 ≤ t := by nlinarith
  have hlo := Nat.le_ceil (t / 2)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ t / 2 by positivity)
  have hmod : ((n % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast Nat.mod_lt n (by omega : 0 < 2)
  have hmcast : (m : ℝ) = 2 * (⌈t / 2⌉₊ : ℝ) + (n % 2 : ℕ) := by simp [m]
  have hmlow : t ≤ (m : ℝ) := by
    rw [hmcast]
    have hmod0 : (0 : ℝ) ≤ ((n % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hmhigh : (m : ℝ) < t + 4 := by rw [hmcast]; linarith
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hm8 : m * 8 ≤ n := by
    have : (m : ℝ) * 8 ≤ n := by nlinarith [sq_nonneg (t - 16)]
    exact_mod_cast this
  refine ⟨m, hm1, (Nat.le_div_iff_mul_le (by omega : 0 < 8)).mpr hm8, ?_, hmlow, ?_⟩
  · simp [m, Nat.add_mod]
  · change (m : ℝ) ≤ 2 * t
    linarith

/-- The same square-root-sized parity bias satisfies the stricter range used
by the explicit one-stage information estimate. -/
theorem exists_parity_bias_sixteenth (n : ℕ) (hn : 1024 ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ (n : ℝ) / 16 ∧ m % 2 = n % 2 ∧
      Real.sqrt n ≤ m ∧ (m : ℝ) ≤ 2 * Real.sqrt n := by
  obtain ⟨m, hm1, hm8, hparity, hlow, hhigh⟩ := exists_parity_bias n hn
  refine ⟨m, hm1, ?_, hparity, hlow, hhigh⟩
  have hs := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hn' : (1024 : ℝ) ≤ n := by exact_mod_cast hn
  have hs32 : 32 ≤ Real.sqrt n := by nlinarith
  nlinarith

end FullJet
