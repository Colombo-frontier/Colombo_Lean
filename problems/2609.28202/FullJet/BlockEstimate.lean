import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

open scoped BigOperators

namespace FullJet

/-- Adjacent-block overlap costs at most four in squared Euclidean norm. -/
theorem adjacent_square_sum_le (T : ℕ) (a : ℕ → ℝ)
    (ha : ∑ j ∈ Finset.range (T + 1), a j ^ 2 ≤ 1) :
    ∑ j ∈ Finset.range T, (a j + a (j + 1)) ^ 2 ≤ 4 := by
  have hleft : ∑ j ∈ Finset.range T, a j ^ 2 ≤ 1 := by
    rw [Finset.sum_range_succ] at ha
    nlinarith [sq_nonneg (a T)]
  have hright : ∑ j ∈ Finset.range T, a (j + 1) ^ 2 ≤ 1 := by
    rw [Finset.sum_range_succ'] at ha
    nlinarith [sq_nonneg (a 0)]
  calc
    _ ≤ ∑ j ∈ Finset.range T, (2 * a j ^ 2 + 2 * a (j + 1) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      nlinarith [sq_nonneg (a j - a (j + 1))]
    _ = 2 * (∑ j ∈ Finset.range T, a j ^ 2) +
        2 * (∑ j ∈ Finset.range T, a (j + 1) ^ 2) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 4 := by linarith

theorem entry_le_two_of_square_sum_le {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (hb : ∑ j ∈ s, b j ^ 2 ≤ 4) {j : ι} (hj : j ∈ s) : b j ≤ 2 := by
  have h := Finset.single_le_sum (fun k (_ : k ∈ s) => sq_nonneg (b k)) hj
  nlinarith

/-- A length-independent product estimate, proved with Cauchy--Schwarz on two
directions and pointwise bounds on the other directions. -/
theorem sum_products_le_two_pow {ι : Type*} (s : Finset ι) (k : ℕ)
    (b : Fin (k + 2) → ι → ℝ)
    (hpos : ∀ l j, j ∈ s → 0 ≤ b l j)
    (hsq : ∀ l, ∑ j ∈ s, b l j ^ 2 ≤ 4) :
    ∑ j ∈ s, ∏ l, b l j ≤ (2 : ℝ) ^ (k + 2) := by
  let u : ι → ℝ := fun j => b 0 j
  let v : ι → ℝ := fun j => b (Fin.succ 0) j
  have huv : ∑ j ∈ s, u j * v j ≤ 4 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s u v
    have hu := hsq 0
    have hv := hsq (Fin.succ 0)
    have hu0 : 0 ≤ ∑ j ∈ s, u j ^ 2 := Finset.sum_nonneg (fun j hj => sq_nonneg _)
    have hv0 : 0 ≤ ∑ j ∈ s, v j ^ 2 := Finset.sum_nonneg (fun j hj => sq_nonneg _)
    have hprod : (∑ j ∈ s, u j ^ 2) * (∑ j ∈ s, v j ^ 2) ≤ 16 := by
      calc
        _ ≤ 4 * 4 := mul_le_mul hu hv hv0 (by norm_num)
        _ = 16 := by norm_num
    nlinarith
  have htail (j : ι) (hj : j ∈ s) :
      (∏ l : Fin k, b l.succ.succ j) ≤ (2 : ℝ) ^ k := by
    calc
      _ ≤ ∏ _l : Fin k, (2 : ℝ) := Finset.prod_le_prod
        (fun l hl => hpos _ _ hj)
        (fun l hl => entry_le_two_of_square_sum_le s _ (hsq _) hj)
      _ = _ := by simp
  calc
    _ ≤ ∑ j ∈ s, (u j * v j) * (2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      dsimp [u, v]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (htail j hj) (mul_nonneg (hpos _ _ hj) (hpos _ _ hj))
    _ = (∑ j ∈ s, u j * v j) * (2 : ℝ) ^ k := by rw [Finset.sum_mul]
    _ ≤ 4 * (2 : ℝ) ^ k := mul_le_mul_of_nonneg_right huv (by positivity)
    _ = (2 : ℝ) ^ (k + 2) := by ring

/-- The central no-chain-length-loss estimate used in the manuscript. -/
theorem adjacent_products_le (T k : ℕ) (a : Fin (k + 2) → ℕ → ℝ)
    (hpos : ∀ l j, 0 ≤ a l j)
    (hnorm : ∀ l, ∑ j ∈ Finset.range (T + 1), a l j ^ 2 ≤ 1) :
    ∑ j ∈ Finset.range T, ∏ l, (a l j + a l (j + 1)) ≤ (2 : ℝ) ^ (k + 2) :=
  sum_products_le_two_pow (Finset.range T) k _
    (fun l j hj => add_nonneg (hpos l j) (hpos l (j + 1)))
    (fun l => adjacent_square_sum_le T (a l) (hnorm l))

/-- Local derivative bounds can be summed with constant `2^order L / ρ`.
Here `d j` is a link derivative evaluated on the chosen unit directions. -/
theorem sum_local_derivatives_le (T k : ℕ) (a : Fin (k + 2) → ℕ → ℝ)
    (d : ℕ → ℝ) (L ρ : ℝ) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hpos : ∀ l j, 0 ≤ a l j)
    (hnorm : ∀ l, ∑ j ∈ Finset.range (T + 1), a l j ^ 2 ≤ 1)
    (hlocal : ∀ j ∈ Finset.range T,
      |d j| ≤ (L / ρ) * ∏ l, (a l j + a l (j + 1))) :
    |∑ j ∈ Finset.range T, d j| ≤ (L / ρ) * (2 : ℝ) ^ (k + 2) := by
  calc
    _ ≤ ∑ j ∈ Finset.range T, |d j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range T, (L / ρ) * ∏ l, (a l j + a l (j + 1)) :=
      Finset.sum_le_sum hlocal
    _ = (L / ρ) * (∑ j ∈ Finset.range T, ∏ l, (a l j + a l (j + 1))) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (adjacent_products_le T k a hpos hnorm)
      (div_nonneg hL hρ.le)

end FullJet
