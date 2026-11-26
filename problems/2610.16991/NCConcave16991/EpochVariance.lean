import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Chronological accumulation of persistent variance with exact refreshes -/

open scoped BigOperators

namespace NCConcave16991

def epochWeight (q t : ℕ) : ℕ := q - t % q

theorem epochWeight_le (q t : ℕ) : epochWeight q t ≤ q := Nat.sub_le _ _

/-- A potential that counts each fresh error increment at most q times. -/
theorem epoch_variance_step {q : ℕ} (hq : 0 < q)
    (error movement : ℕ → ℝ) {α : ℝ} (hα : 0 ≤ α)
    (hm : ∀ t, 0 ≤ movement t)
    (hreset : ∀ t, t % q = 0 → error t = 0)
    (hstep : ∀ t, (t + 1) % q ≠ 0 → error (t + 1) ≤ error t + α * movement t)
    (t : ℕ) :
    error t + (epochWeight q (t + 1) : ℝ) * error (t + 1) ≤
      (epochWeight q t : ℝ) * error t + (q : ℝ) * α * movement t := by
  have hr := Nat.mod_lt t hq
  have hmod : (t + 1) % q = (t % q + 1) % q := by
    rw [Nat.add_mod, Nat.add_mod (t % q) 1 q, Nat.mod_mod]
  by_cases hlast : t % q + 1 = q
  · have hn : (t + 1) % q = 0 := by rw [hmod, hlast, Nat.mod_self]
    have hw : epochWeight q t = 1 := by dsimp [epochWeight]; omega
    rw [hreset _ hn, hw]
    simp only [Nat.cast_one, one_mul, mul_zero, add_zero]
    have hp : 0 ≤ (q : ℝ) * α * movement t :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg q) hα) (hm t)
    linarith
  · have hless : t % q + 1 < q := by omega
    have hn : (t + 1) % q = t % q + 1 := by rw [hmod, Nat.mod_eq_of_lt hless]
    have hn0 : (t + 1) % q ≠ 0 := by omega
    have hw : epochWeight q t = epochWeight q (t + 1) + 1 := by
      dsimp [epochWeight]
      omega
    have hwr : (epochWeight q t : ℝ) = (epochWeight q (t + 1) : ℝ) + 1 := by
      exact_mod_cast hw
    have hwl : (epochWeight q (t + 1) : ℝ) ≤ q := by
      exact_mod_cast epochWeight_le q (t + 1)
    have hwn : (0 : ℝ) ≤ epochWeight q (t + 1) := by positivity
    have hs := mul_le_mul_of_nonneg_left (hstep t hn0) hwn
    have hmα : 0 ≤ α * movement t := mul_nonneg hα (hm t)
    have hb := mul_le_mul_of_nonneg_right hwl hmα
    calc
      error t + (epochWeight q (t + 1) : ℝ) * error (t + 1) ≤
          error t + (epochWeight q (t + 1) : ℝ) * (error t + α * movement t) :=
        add_le_add_right hs _
      _ = ((epochWeight q (t + 1) : ℝ) + 1) * error t +
          (epochWeight q (t + 1) : ℝ) * (α * movement t) := by ring
      _ ≤ ((epochWeight q (t + 1) : ℝ) + 1) * error t + (q : ℝ) * (α * movement t) :=
        add_le_add_right hb _
      _ = (epochWeight q t : ℝ) * error t + (q : ℝ) * α * movement t := by
        rw [hwr]
        ring

/-- This includes a partially completed final epoch and arbitrary nonnegative
movement sequences. No separate per-epoch bound is assumed. -/
theorem epoch_variance_sum {q : ℕ} (hq : 0 < q)
    (error movement : ℕ → ℝ) {α : ℝ} (hα : 0 ≤ α)
    (he : ∀ t, 0 ≤ error t) (hm : ∀ t, 0 ≤ movement t)
    (hreset : ∀ t, t % q = 0 → error t = 0)
    (hstep : ∀ t, (t + 1) % q ≠ 0 → error (t + 1) ≤ error t + α * movement t)
    (S : ℕ) :
    ∑ t ∈ Finset.range S, error t ≤ (q : ℝ) * α * ∑ t ∈ Finset.range S, movement t := by
  have htel : ∀ k, (∑ t ∈ Finset.range k, error t) +
      (epochWeight q k : ℝ) * error k ≤
        (epochWeight q 0 : ℝ) * error 0 +
          (q : ℝ) * α * ∑ t ∈ Finset.range k, movement t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := epoch_variance_step hq error movement hα hm hreset hstep k
      simp only [Finset.sum_range_succ]
      nlinarith
  have hz : error 0 = 0 := hreset 0 (by simp)
  have ht := htel S
  rw [hz, mul_zero, zero_add] at ht
  have hp : 0 ≤ (epochWeight q S : ℝ) * error S := mul_nonneg (by positivity) (he S)
  linarith

end NCConcave16991
