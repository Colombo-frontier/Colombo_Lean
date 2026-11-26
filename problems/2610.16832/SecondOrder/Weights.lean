import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

open scoped BigOperators

namespace SecondOrder
noncomputable section

/-- `P p` in the manuscript, with zero-based gates. -/
def tailProduct (b : ℕ → ℝ) (n p : ℕ) : ℝ := ∏ k ∈ Finset.Ico p n, (1-b k)

theorem tailProduct_step (b : ℕ → ℝ) {n p : ℕ} (hp : p < n) :
    tailProduct b n p = (1-b p)*tailProduct b n (p+1) := by
  exact Finset.prod_eq_prod_Ico_succ_bot hp (fun k => 1-b k)

theorem tailProduct_self (b : ℕ → ℝ) (n : ℕ) : tailProduct b n n = 1 := by
  simp [tailProduct]

theorem reverse_weight_eq_difference (b : ℕ → ℝ) {n p : ℕ} (hp : p < n) :
    b p * tailProduct b n (p+1) = tailProduct b n (p+1) - tailProduct b n p := by
  rw [tailProduct_step b hp]
  ring

theorem reverse_weights_sum (b : ℕ → ℝ) (n : ℕ) :
    tailProduct b n 0 + ∑ p ∈ Finset.range n, b p * tailProduct b n (p+1) = 1 := by
  have hsum : (∑ p ∈ Finset.range n, b p * tailProduct b n (p+1)) =
      tailProduct b n n - tailProduct b n 0 := by
    trans ∑ p ∈ Finset.range n, (tailProduct b n (p+1) - tailProduct b n p)
    · exact Finset.sum_congr rfl (fun p hp => reverse_weight_eq_difference b (Finset.mem_range.mp hp))
    · exact Finset.sum_range_sub (tailProduct b n) n
  rw [hsum, tailProduct_self]
  ring

theorem tailProduct_nonneg {b : ℕ → ℝ} {n : ℕ}
    (hb : ∀ k < n, b k ≤ 1) (p : ℕ) : 0 ≤ tailProduct b n p := by
  apply Finset.prod_nonneg
  intro k hk
  exact sub_nonneg.mpr (hb k (Finset.mem_Ico.mp hk).2)

/-- Value part of the selector inequality, for the actual reverse products. -/
theorem reverse_selector_value_bound {b : ℕ → ℝ} {n : ℕ} {v : ℝ}
    (hb : ∀ k < n, 0 ≤ b k ∧ b k ≤ 1)
    (V : ℕ → ℝ) (hV : ∀ k ≤ n, |V k| ≤ v) :
    |tailProduct b n 0 * V 0 +
      ∑ p ∈ Finset.range n, b p * tailProduct b n (p+1) * V (p+1)| ≤ v := by
  have htail := tailProduct_nonneg (fun k hk => (hb k hk).2)
  calc
    _ ≤ |tailProduct b n 0 * V 0| +
        ∑ p ∈ Finset.range n, |b p * tailProduct b n (p+1) * V (p+1)| :=
      (abs_add_le _ _).trans (add_le_add_left (Finset.abs_sum_le_sum_abs _ _) _)
    _ ≤ tailProduct b n 0 * v + ∑ p ∈ Finset.range n,
        b p * tailProduct b n (p+1) * v := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (htail 0)]
        exact mul_le_mul_of_nonneg_left (hV 0 (Nat.zero_le n)) (htail 0)
      · apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_range.mp hp
        have hw : 0 ≤ b p * tailProduct b n (p+1) := mul_nonneg (hb p hp').1 (htail _)
        rw [abs_mul, abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_left (hV (p+1) (by omega)) hw
    _ = (tailProduct b n 0 + ∑ p ∈ Finset.range n, b p * tailProduct b n (p+1)) * v := by
      rw [add_mul, Finset.sum_mul]
    _ = v := by rw [reverse_weights_sum, one_mul]

theorem frontier_scalar_cancellation (a W Z : ℝ) : a*W + a*(Z-W) = a*Z := by ring

/-- Equality as scalar functions implies equality of *all* first two derivatives,
without treating the value, gradient and Hessian as independent channels. -/
theorem frontier_full_derivative_cancellation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a W Z : E → ℝ) :
    (fun x => a x * W x + a x * (Z x-W x)) = (fun x => a x * Z x) ∧
    fderiv ℝ (fun x => a x * W x + a x * (Z x-W x)) =
      fderiv ℝ (fun x => a x * Z x) ∧
    fderiv ℝ (fderiv ℝ (fun x => a x * W x + a x * (Z x-W x))) =
      fderiv ℝ (fderiv ℝ (fun x => a x * Z x)) := by
  have h : (fun x => a x * W x + a x * (Z x-W x)) = (fun x => a x * Z x) := by
    funext x
    ring
  exact ⟨h, congrArg (fderiv ℝ) h, congrArg (fun f => fderiv ℝ (fderiv ℝ f)) h⟩

theorem regularized_gate_variance (b δ : ℝ) :
    (δ+(1-2*δ)*b)*(1-(δ+(1-2*δ)*b)) =
      (1-2*δ)^2*b*(1-b) + δ*(1-δ) := by ring

end
end SecondOrder
