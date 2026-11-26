import LowRank.GaussianOperatorTail
import Mathlib.Tactic

/-! The manuscript's Gaussian operator-norm input, proved from the verified
finite-net Gaussian bound in the local LowRank library. Entry variance is 1.
The constants 32 and 1/32 are deliberately conservative. -/
namespace Matvec
open MeasureTheory

theorem gaussian_operator_norm_tail (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (LowRank.iidMatrixLaw N N 1).real
      {G | 32 * Real.sqrt N + t < ‖LowRank.matrixEuclideanMap G‖} ≤
      2 * Real.exp (-(t ^ 2) / 32) := by
  have hbase := LowRank.iidMatrixLaw_operator_tail N N 1
    (t := 8 * Real.sqrt N + t / 4) (by positivity)
  norm_num only [NNReal.coe_one, mul_one] at hbase
  have hscale : 4 * (8 * Real.sqrt (N : ℝ) + t / 4) =
      32 * Real.sqrt N + t := by ring
  rw [hscale] at hbase
  refine hbase.trans ?_
  have hexp : (5 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hp : (5 : ℝ) ^ (N + N) ≤ Real.exp (4 * ((N + N : ℕ) : ℝ)) := by
    simpa only [Real.exp_nat_mul, mul_comm] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hexp (N + N)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hnonneg : 0 ≤ Real.sqrt (N : ℝ) * t := mul_nonneg (Real.sqrt_nonneg _) ht
  have harith : 4 * ((N + N : ℕ) : ℝ) -
      (8 * Real.sqrt (N : ℝ) + t / 4) ^ 2 / (2 * (1 : ℝ)) ≤ -(t ^ 2) / 32 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  calc
    _ ≤ 2 * Real.exp (4 * ((N + N : ℕ) : ℝ)) *
        Real.exp (-(8 * Real.sqrt (N : ℝ) + t / 4) ^ 2 / (2 * (1 : ℝ))) := by
      norm_num only [mul_one]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by norm_num)) (Real.exp_nonneg _)
    _ = 2 * Real.exp (4 * ((N + N : ℕ) : ℝ) -
        (8 * Real.sqrt (N : ℝ) + t / 4) ^ 2 / (2 * (1 : ℝ))) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harith) (by norm_num)

end Matvec
