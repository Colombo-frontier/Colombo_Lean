import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! The exact finite stick-breaking weights used in the leaf and hierarchy.
This verifies their convex-partition algebra, not their derivative estimates. -/

namespace GradientHessian.Selectors

open scoped BigOperators

def prefixProduct (port : ℕ → ℝ) (i : ℕ) : ℝ := ∏ j ∈ Finset.range i, port j
def weight (port : ℕ → ℝ) (i : ℕ) : ℝ := (1 - port i) * prefixProduct port i

theorem partition (port : ℕ → ℝ) (b : ℕ) :
    (∑ i ∈ Finset.range b, weight port i) + prefixProduct port b = 1 := by
  induction b with
  | zero => simp [prefixProduct]
  | succ b ih =>
    simp only [Finset.sum_range_succ, weight, prefixProduct, Finset.prod_range_succ] at *
    nlinarith [ih]

theorem prefix_nonneg {port : ℕ → ℝ} {b : ℕ}
    (h : ∀ i < b, 0 ≤ port i) : 0 ≤ prefixProduct port b := by
  exact Finset.prod_nonneg fun i hi => h i (Finset.mem_range.mp hi)

theorem weight_nonneg {port : ℕ → ℝ} {b i : ℕ}
    (h : ∀ j < b, port j ∈ Set.Icc (0 : ℝ) 1) (hi : i < b) :
    0 ≤ weight port i := by
  exact mul_nonneg (sub_nonneg.mpr (h i hi).2)
    (prefix_nonneg fun j hj => (h j (hj.trans hi)).1)

theorem weighted_payload_bounds {port payload : ℕ → ℝ} {terminal lower upper : ℝ}
    {b : ℕ} (hp : ∀ i < b, port i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i < b, payload i ∈ Set.Icc lower upper)
    (ht : terminal ∈ Set.Icc lower upper) :
    (∑ i ∈ Finset.range b, weight port i * payload i) + prefixProduct port b * terminal ∈
      Set.Icc lower upper := by
  have hprefix := prefix_nonneg (fun i hi => (hp i hi).1)
  have hpartition := partition port b
  constructor
  · calc
      lower = (∑ i ∈ Finset.range b, weight port i * lower) + prefixProduct port b * lower := by
        rw [← Finset.sum_mul, ← add_mul, hpartition, one_mul]
      _ ≤ _ := add_le_add (Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hv i (Finset.mem_range.mp hi)).1
          (weight_nonneg hp (Finset.mem_range.mp hi)))
        (mul_le_mul_of_nonneg_left ht.1 hprefix)
  · calc
      _ ≤ (∑ i ∈ Finset.range b, weight port i * upper) + prefixProduct port b * upper :=
        add_le_add (Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (hv i (Finset.mem_range.mp hi)).2
            (weight_nonneg hp (Finset.mem_range.mp hi)))
          (mul_le_mul_of_nonneg_left ht.2 hprefix)
      _ = upper := by rw [← Finset.sum_mul, ← add_mul, hpartition, one_mul]

/-- A completed prefixProduct is exactly transparent, including at plateau endpoints. -/
theorem prefix_eq_one {port : ℕ → ℝ} {b : ℕ} (h : ∀ i < b, port i = 1) :
    prefixProduct port b = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  exact h i (Finset.mem_range.mp hi)

/-- A zero port eliminates all strictly later weights. -/
theorem weight_zero_after {port : ℕ → ℝ} {i j : ℕ}
    (hi : port i = 0) (hij : i < j) : weight port j = 0 := by
  have hp : prefixProduct port j = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.mpr hij) hi
  simp [weight, hp]

end GradientHessian.Selectors
