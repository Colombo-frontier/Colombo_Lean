import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Hierarchy energy and reliability arithmetic

Exact finite-depth estimates for the recurrence in `eq:energy-rec`, and the
geometric series used in `eq:outer-repair-charge`. These are arithmetic
consequences, not proofs that a random construction satisfies its input bounds.
-/

noncomputable section

namespace GradientHessian.Reliability

open scoped BigOperators

/-- Index zero is height one; the first recurrence step is height two. -/
def energy (A₁ R₀ K : ℝ) : ℕ → ℝ
  | 0 => A₁
  | j + 1 => 8 * (energy A₁ R₀ K j + 768 * (K * R₀ * 6 ^ j))
      + 8 * 208 * (R₀ * 3 ^ j)

theorem energy_closed_form (A₁ R₀ K : ℝ) (j : ℕ) :
    energy A₁ R₀ K j =
      8 ^ j * A₁ + 3072 * K * R₀ * (8 ^ j - 6 ^ j)
        + (1664 / 5 : ℝ) * R₀ * (8 ^ j - 3 ^ j) := by
  induction j with
  | zero => simp [energy]
  | succ j ih => rw [energy, ih]; simp only [pow_succ]; ring

theorem energy_upper_bound {A₁ R₀ K : ℝ} (hR : 0 ≤ R₀) (hK : 0 ≤ K) (j : ℕ) :
    energy A₁ R₀ K j ≤ 8 ^ j * (A₁ + 3072 * K * R₀ + (1664 / 5 : ℝ) * R₀) := by
  rw [energy_closed_form]
  have h₆ : 0 ≤ 3072 * K * R₀ * (6 : ℝ) ^ j := by positivity
  have h₃ : 0 ≤ (1664 / 5 : ℝ) * R₀ * (3 : ℝ) ^ j := by positivity
  nlinarith

/-- Finite geometric-series bound, retaining the terminal remainder. -/
theorem geometric_sum_with_remainder {r : ℝ} (N : ℕ) :
    (1 - r) * (∑ j ∈ Finset.range N, r ^ j) = 1 - r ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring

theorem geometric_sum_le_two {r : ℝ} (hr₀ : 0 ≤ r) (hr : r ≤ 1 / 2) (N : ℕ) :
    (∑ j ∈ Finset.range N, r ^ j) ≤ 2 := by
  have hs : 0 ≤ ∑ j ∈ Finset.range N, r ^ j := Finset.sum_nonneg (by
    intro i _; positivity)
  have hp : 0 ≤ r ^ N := pow_nonneg hr₀ _
  have hi := geometric_sum_with_remainder (r := r) N
  nlinarith

/-- The normalized cost series after extracting the radius-ratio prefactor. -/
theorem reliability_series_bound {a r : ℝ}
    (ha : 0 ≤ a) (hr₀ : 0 ≤ r) (hr : r ≤ 1 / 2) (N : ℕ) :
    (∑ j ∈ Finset.range N, 128 * a * r ^ j) ≤ 256 * a := by
  rw [← Finset.mul_sum]
  have := mul_le_mul_of_nonneg_left (geometric_sum_le_two hr₀ hr N)
    (show 0 ≤ 128 * a by positivity)
  nlinarith

/-- Exact level cost at fixed reliability dimension eight, as in the paper. -/
def fixedDimensionCost (K : ℝ) (j : ℕ) : ℝ :=
  128 * (6 / K) ^ 7 * (1 / 16 : ℝ) ^ j

theorem fixed_dimension_cost_eq (K : ℝ) (j : ℕ) :
    (8 : ℝ) ^ (j + 2) * 2 * (6 / (K * 2 ^ j)) ^ 7 = fixedDimensionCost K j := by
  have hp : ((2 : ℝ) ^ j) ^ 7 = (128 : ℝ) ^ j := by
    rw [← pow_mul, Nat.mul_comm j 7, pow_mul]
    norm_num
  have hd : (1 / 16 : ℝ) ^ j = (8 : ℝ) ^ j / (128 : ℝ) ^ j := by
    rw [← div_pow]
    norm_num
  rw [fixedDimensionCost, hd]
  simp only [pow_add, div_pow, mul_pow]
  rw [hp]
  ring

theorem fixed_dimension_tail (K : ℝ) (hK : 0 < K) (start count : ℕ) :
    (∑ j ∈ Finset.range count, fixedDimensionCost K (start + j)) ≤
      256 * (6 / K) ^ 7 * (1 / 16 : ℝ) ^ start := by
  simp only [fixedDimensionCost, pow_add]
  have h := reliability_series_bound
    (a := (6 / K) ^ 7 * (1 / 16 : ℝ) ^ start)
    (r := (1 / 16 : ℝ)) (by positivity) (by norm_num) (by norm_num) count
  simpa only [mul_assoc] using h

end GradientHessian.Reliability
