import SecondOrder.DyadicEnergy
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators

namespace SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact telescoping over a partition, with no inherited estimator errors. -/
theorem chord_partition_telescopes (G : ℕ → E) (cut : ℕ → ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (G (cut (i+1))-G (cut i))) = G (cut n)-G (cut 0) :=
  Finset.sum_range_sub (fun i => G (cut i)) n

/-- Uniform tracker accuracy on local success. The count of *active* chords is
bounded by L; the total number of earlier estimates is irrelevant. -/
theorem tracker_accuracy (G : ℕ → E) (cut : ℕ → ℕ) (n L : ℕ) (anchor : E)
    (chord : ℕ → E) {τ ρ : ℝ} (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ)
    (hn : n ≤ L) (ha : ‖anchor-G (cut 0)‖ ≤ τ/4)
    (hc : ∀ i < n, ‖chord i-(G (cut (i+1))-G (cut i))‖ ≤ ρ)
    (hbudget : (L:ℝ)*ρ ≤ τ/4) :
    ‖anchor+(∑ i ∈ Finset.range n, chord i)-G (cut n)‖ ≤ τ/2 := by
  have heq : anchor+(∑ i ∈ Finset.range n, chord i)-G (cut n) =
      (anchor-G (cut 0)) + ∑ i ∈ Finset.range n, (chord i-(G (cut (i+1))-G (cut i))) := by
    rw [Finset.sum_sub_distrib, chord_partition_telescopes]
    abel
  rw [heq]
  have hcSum : ‖∑ i ∈ Finset.range n, (chord i-(G (cut (i+1))-G (cut i)))‖ ≤ (n:ℝ)*ρ := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ i ∈ Finset.range n, ρ := Finset.sum_le_sum (fun i hi => hc i (Finset.mem_range.mp hi))
      _ = _ := by simp
  have hnρ := mul_le_mul_of_nonneg_right (by exact_mod_cast hn : (n:ℝ) ≤ L) hρ
  have ht := norm_add_le (anchor-G (cut 0))
    (∑ i ∈ Finset.range n, (chord i-(G (cut (i+1))-G (cut i))))
  linarith

/-- Fewer than two tree nodes per physical move, in the exact floor-count form.
The bound covers every dyadic level, including empty levels. -/
theorem binary_node_count (M L : ℕ) : (∑ l ∈ Finset.range L, M / 2^l) ≤ 2*M := by
  induction L generalizing M with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ']
    have hshift : (∑ l ∈ Finset.range L, M/2^(l+1)) = ∑ l ∈ Finset.range L, (M/2)/2^l := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Nat.div_div_eq_div_mul, pow_succ]
      congr 1
      omega
    rw [hshift]
    simp only [pow_zero, Nat.div_one]
    have hb := ih (M/2)
    omega

end SecondOrder
