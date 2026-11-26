/- Adapted from the proved radial-calculus fragments in ../0105_formalization/Manuscript0105/ChainAverage.lean. No assumed lower bounds are imported. -/
import NCConcave16991.DenseSmoothEncodingAverage

/-!
# Averaging the component radial chain

This is the finite-sum algebra behind equation `(radial-average)`.
-/

open scoped BigOperators

namespace NCConcave16991.DenseSmooth

def abstractComponentRadialChain {n T : ℕ}
    (qtilde : Fin n → Fin (T + 1) → ℝ) (gate : Fin T → ℝ)
    (quadratic : ℝ) (i : Fin n) : ℝ :=
  -qtilde i 0 - ∑ j, gate j * (qtilde i j.succ + 1) + quadratic

theorem average_abstractComponentRadialChain
    {n T : ℕ} [NeZero n]
    (qtilde : Fin n → Fin (T + 1) → ℝ) (q : Fin (T + 1) → ℝ)
    (gate : Fin T → ℝ) (quadratic : ℝ)
    (hmean : ∀ j, (∑ i, qtilde i j) / n = q j) :
    (∑ i, abstractComponentRadialChain qtilde gate quadratic i) / n =
      abstractRadialChain q gate quadratic := by
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.pos_of_ne_zero (NeZero.ne n)))
  have hmeanSum (j : Fin (T + 1)) : ∑ i, qtilde i j = (n : ℝ) * q j := by
    have hj := (div_eq_iff hn).mp (hmean j)
    simpa [mul_comm] using hj
  have hlinkSum (j : Fin T) :
      ∑ i, gate j * (qtilde i j.succ + 1) =
        (n : ℝ) * (gate j * (q j.succ + 1)) := by
    rw [← Finset.mul_sum]
    rw [Finset.sum_add_distrib, hmeanSum]
    simp
    ring
  apply (div_eq_iff hn).2
  simp only [abstractComponentRadialChain, abstractRadialChain]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp_rw [hlinkSum]
  rw [← Finset.mul_sum]
  rw [hmeanSum]
  simp
  ring

end NCConcave16991.DenseSmooth
