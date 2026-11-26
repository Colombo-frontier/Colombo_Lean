import GradientHessian.Reliability
import Mathlib.Algebra.BigOperators.Intervals

/-!
Exact discrete allocation formulas used in `eq:level-dimension` and the
dimension count following `eq:physical-dimension-log`. The geometric estimate
is the low-level series estimate used after `eq:outer-repair-charge`.
Neither dimension asymptotics nor the probabilistic repair expectation is
assumed or claimed here.
-/

namespace GradientHessian.Allocation

open scoped BigOperators

def levelDimension (pLow cutoff q : ℕ) : ℕ := if q < cutoff then pLow else 8

theorem sum_two_regimes (low high cutoff N : ℕ) :
    (∑ j ∈ Finset.range N, if j < cutoff then low else high) =
      low * min N cutoff + high * (N-cutoff) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : N < cutoff
    · have hs : N+1 ≤ cutoff := h
      simp only [if_pos h, min_eq_left h.le, min_eq_left hs,
        Nat.sub_eq_zero_of_le h.le, Nat.sub_eq_zero_of_le hs, mul_zero, add_zero]
      ring
    · have hc : cutoff ≤ N := le_of_not_gt h
      have hs : N+1-cutoff = N-cutoff+1 := by omega
      simp only [if_neg h, min_eq_right hc, min_eq_right (hc.trans (Nat.le_succ N)), hs]
      ring

/-- There are `min L (cutoff-1)-1` low-dimensional levels, and
`L+1-cutoff` fixed-dimensional levels, with natural subtraction. -/
theorem level_dimension_sum (pLow cutoff L : ℕ) (hc : 2 ≤ cutoff) :
    (∑ q ∈ Finset.Icc 2 L, levelDimension pLow cutoff q) =
      pLow * (min L (cutoff-1)-1) + 8 * (L+1-cutoff) := by
  rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
  have hi : ∀ j : ℕ, 2+j < cutoff ↔ j < cutoff-2 := by omega
  simp only [levelDimension, hi]
  rw [sum_two_regimes]
  congr 1
  · congr 1
    omega
  · congr 1
    omega

/-- The number of allocated coordinates at heights two through `L` is
bounded linearly in depth once the cutoff and low-level allocation are fixed. -/
theorem level_dimension_sum_bound (pLow cutoff L : ℕ) (hc : 2 ≤ cutoff) :
    (∑ q ∈ Finset.Icc 2 L, levelDimension pLow cutoff q) ≤
      pLow * (cutoff-2) + 8 * L := by
  rw [level_dimension_sum pLow cutoff L hc]
  apply Nat.add_le_add
  · apply Nat.mul_le_mul_left
    omega
  · apply Nat.mul_le_mul_left
    omega

/-- `j=0` is physical height two. -/
noncomputable def levelCost (K : ℝ) (p j : ℕ) : ℝ :=
  (8 : ℝ)^(j+2) * 2 * (6/(K * 2^j))^(p-1)

theorem level_cost_geometric (K : ℝ) (p j : ℕ) :
    levelCost K p j = 128*(6/K)^(p-1)*(8/(2:ℝ)^(p-1))^j := by
  have hp : ((2:ℝ)^j)^(p-1) = ((2:ℝ)^(p-1))^j := by
    rw [← pow_mul, Nat.mul_comm j (p-1), pow_mul]
  simp only [levelCost, pow_add, div_pow, mul_pow]
  rw [hp]
  ring

theorem level_cost_ratio_bound {p : ℕ} (hp : 8 ≤ p) :
    0 ≤ (8:ℝ)/2^(p-1) ∧ (8:ℝ)/2^(p-1) ≤ 1/2 := by
  constructor
  · positivity
  · have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
      (show 7 ≤ p-1 by omega)
    norm_num at hpow
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^(p-1))).mpr
    linarith

/-- The manuscript's low-level geometric bound, for any finite number of levels
and any integer reliability dimension at least eight. -/
theorem low_dimension_cost_bound {K : ℝ} (hK : 0 < K) {p : ℕ}
    (hp : 8 ≤ p) (count : ℕ) :
    (∑ j ∈ Finset.range count, levelCost K p j) ≤ 256*(6/K)^(p-1) := by
  simp only [level_cost_geometric]
  exact Reliability.reliability_series_bound (by positivity)
    (level_cost_ratio_bound hp).1 (level_cost_ratio_bound hp).2 count

end GradientHessian.Allocation
