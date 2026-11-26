import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Scalar inequalities in the row-information argument

These are the deterministic estimates used in Lemma `lem:self-info` before the measure-theoretic
chain rule is applied.
-/

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

/-- The conditional next-cell Bernoulli parameter remains in `[7/16,9/16]`. -/
theorem nextSignProbability_deviation
    {n m d sigma theta : ℝ}
    (hm : 0 ≤ m) (hd : 0 ≤ d) (hnd : d < n)
    (hbudget : 8 * m + 9 * d ≤ n)
    (hsigma : |sigma| ≤ d) (htheta : theta = 1 ∨ theta = -1) :
    |(n + m * theta - d - sigma) / (2 * (n - d)) - 1 / 2| ≤ 1 / 16 := by
  have hden : 0 < 2 * (n - d) := by positivity
  have hthetaAbs : |theta| = 1 := by rcases htheta with rfl | rfl <;> norm_num
  have hnum : |m * theta - sigma| ≤ m + d := by
    calc
      |m * theta - sigma| ≤ |m * theta| + |sigma| := abs_sub _ _
      _ ≤ m + d := by rw [abs_mul, abs_of_nonneg hm, hthetaAbs, mul_one]; linarith
  have hratio : (m + d) / (2 * (n - d)) ≤ 1 / 16 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hnd0 : n - d ≠ 0 := by linarith
  rw [show (n + m * theta - d - sigma) / (2 * (n - d)) - 1 / 2 =
      (m * theta - sigma) / (2 * (n - d)) by field_simp [hnd0]; ring]
  rw [abs_div, abs_of_pos hden]
  exact (div_le_div_of_nonneg_right hnum hden.le).trans hratio

theorem nextSignProbability_mem_Icc
    {n m d sigma theta : ℝ}
    (hm : 0 ≤ m) (hd : 0 ≤ d) (hnd : d < n)
    (hbudget : 8 * m + 9 * d ≤ n)
    (hsigma : |sigma| ≤ d) (htheta : theta = 1 ∨ theta = -1) :
    (n + m * theta - d - sigma) / (2 * (n - d)) ∈
      Set.Icc (7 / 16 : ℝ) (9 / 16) := by
  have h := nextSignProbability_deviation hm hd hnd hbudget hsigma htheta
  rw [abs_le] at h
  constructor <;> linarith

/-- The posterior factor `π(1-π)` costs at most `1/4`, giving `32/63` from `128/63`. -/
theorem binaryInformation_coefficient_bound
    {pi x : ℝ} (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1) :
    (128 / 63 : ℝ) * pi * (1 - pi) * x ^ 2 ≤
      (32 / 63 : ℝ) * x ^ 2 := by
  have hquarter : pi * (1 - pi) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (pi - 1 / 2)]
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  nlinarith [mul_le_mul_of_nonneg_right hquarter hx]

/-- Monotonicity of `d ↦ m/(n-d)` gives the second inequality in `(self-info)`. -/
theorem selfInfo_ratio_sum_le
    {n m r : ℕ} (hr : r < n) :
    ∑ d ∈ Finset.range r, ((m : ℝ) / ((n : ℝ) - d)) ^ 2 ≤
      (r : ℝ) * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 := by
  have hnrCast : (r : ℝ) < n := by exact_mod_cast hr
  have hnr : (0 : ℝ) < (n : ℝ) - r := by linarith
  calc
    ∑ d ∈ Finset.range r, ((m : ℝ) / ((n : ℝ) - d)) ^ 2
        ≤ ∑ _d ∈ Finset.range r, ((m : ℝ) / ((n : ℝ) - r)) ^ 2 := by
          apply Finset.sum_le_sum
          intro d hdmem
          have hdr : d < r := Finset.mem_range.mp hdmem
          have hdrCast : (d : ℝ) ≤ r := by exact_mod_cast Nat.le_of_lt hdr
          have hden : (n : ℝ) - r ≤ (n : ℝ) - d := by linarith
          have hdpos : (0 : ℝ) < (n : ℝ) - d := hnr.trans_le hden
          have hdiv : (m : ℝ) / ((n : ℝ) - d) ≤ (m : ℝ) / ((n : ℝ) - r) :=
            div_le_div_of_nonneg_left (by positivity) hnr hden
          exact pow_le_pow_left₀ (by positivity) hdiv 2
    _ = (r : ℝ) * ((m : ℝ) / ((n : ℝ) - r)) ^ 2 := by
      simp

end NCConcave16991.DenseWeakHiding

/- Adapted from the local 0105_formalization/Manuscript0105/InformationArithmetic.lean. These analytic lemmas are reused for the cited dense weak hiding dependency; they do not assert its oracle lower bound. -/
