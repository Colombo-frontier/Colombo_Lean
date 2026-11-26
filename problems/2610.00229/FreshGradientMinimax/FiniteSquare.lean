import FreshGradientMinimax.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Finite Cauchy bounds used to convert the exact regularization identity
into a squared-gradient estimate. No independence is required. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] {ι : Type*}

theorem norm_sum_sq_le_card (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
    _ ≤ _ := by
      simpa only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun _ => (1 : ℝ))

theorem norm_sub_sum_sq_le (x : E) (f : ℕ → E) (N : ℕ) :
    ‖x - ∑ i ∈ Finset.range N, f i‖ ^ 2 ≤
      (N + 1 : ℕ) * (‖x‖ ^ 2 + ∑ i ∈ Finset.range N, ‖f i‖ ^ 2) := by
  let g : ℕ → E := fun j => Nat.rec x (fun i _ => -f i) j
  have hs : (∑ j ∈ Finset.range (N + 1), g j) = x - ∑ i ∈ Finset.range N, f i := by
    rw [Finset.sum_range_succ']
    simp only [g, Nat.rec_zero, Nat.rec_add_one, Finset.sum_neg_distrib]
    abel
  have hq : (∑ j ∈ Finset.range (N + 1), ‖g j‖ ^ 2) =
      ‖x‖ ^ 2 + ∑ i ∈ Finset.range N, ‖f i‖ ^ 2 := by
    rw [Finset.sum_range_succ']
    simp only [g, Nat.rec_zero, Nat.rec_add_one, norm_neg]
    ring
  simpa only [hs, hq, Finset.card_range] using norm_sum_sq_le_card (Finset.range (N + 1)) g

end FreshGradientMinimax
