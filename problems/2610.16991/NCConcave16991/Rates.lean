import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact rate algebra for arXiv:2610.16991v2

This file proves the real-variable comparisons behind the three regimes of
Theorem 3.1. It does not assert an oracle-complexity theorem: the algorithmic
upper bounds and randomized oracle lower bounds are separate mathematical tasks.
The powers of `n` below are actual real powers, not independent scale parameters.
-/

namespace NCConcave16991

noncomputable section

/-- The paper's clipped dimensionless diameter `B̄`. -/
def clippedDiameter (B : ℝ) : ℝ := max 1 B

/-- The accuracy-dependent coefficient `𝓕(n,B)` of equation (8). -/
def rate (n B : ℝ) : ℝ :=
  min (n ^ (1 / 2 : ℝ) * clippedDiameter B + clippedDiameter B ^ 4)
      (n ^ (3 / 4 : ℝ) * clippedDiameter B)

/-- The coefficient supplied by the optimization-type lower bound (13). -/
def optimizationLower (n B : ℝ) : ℝ :=
  min (n ^ (1 / 2 : ℝ) * clippedDiameter B) (n ^ (3 / 4 : ℝ))

/-- The coefficient supplied by the cone/branch lower bound (14). -/
def diameterLower (n B : ℝ) : ℝ :=
  min (B ^ 4) (n ^ (3 / 4 : ℝ) * B)

theorem clippedDiameter_one_le (B : ℝ) : 1 ≤ clippedDiameter B := le_max_left _ _

theorem clippedDiameter_nonneg (B : ℝ) : 0 ≤ clippedDiameter B :=
  le_trans (by norm_num) (clippedDiameter_one_le B)

theorem le_clippedDiameter (B : ℝ) : B ≤ clippedDiameter B := le_max_right _ _

theorem clippedDiameter_of_le_one {B : ℝ} (hB : B ≤ 1) : clippedDiameter B = 1 :=
  max_eq_left hB

theorem clippedDiameter_of_one_le {B : ℝ} (hB : 1 ≤ B) : clippedDiameter B = B :=
  max_eq_right hB

theorem rate_eq_sqrt (n B : ℝ) :
    rate n B = min (Real.sqrt n * clippedDiameter B + clippedDiameter B ^ 4)
      (n ^ (3 / 4 : ℝ) * clippedDiameter B) := by
  rw [rate, Real.sqrt_eq_rpow]

private theorem rpow_cube (n a : ℝ) (hn : 0 ≤ n) :
    (n ^ a) ^ (3 : ℕ) = n ^ (a * 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  norm_num

private theorem sixth_cube {n : ℝ} (hn : 0 ≤ n) :
    (n ^ (1 / 6 : ℝ)) ^ (3 : ℕ) = n ^ (1 / 2 : ℝ) := by
  rw [rpow_cube n (1 / 6 : ℝ) hn]
  norm_num

private theorem quarter_cube {n : ℝ} (hn : 0 ≤ n) :
    (n ^ (1 / 4 : ℝ)) ^ (3 : ℕ) = n ^ (3 / 4 : ℝ) := by
  rw [rpow_cube n (1 / 4 : ℝ) hn]
  norm_num

private theorem half_mul_quarter {n : ℝ} (hn : 0 < n) :
    n ^ (1 / 2 : ℝ) * n ^ (1 / 4 : ℝ) = n ^ (3 / 4 : ℝ) := by
  rw [← Real.rpow_add hn]
  norm_num

theorem half_le_three_quarters {n : ℝ} (hn : 1 ≤ n) :
    n ^ (1 / 2 : ℝ) ≤ n ^ (3 / 4 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hn (by norm_num)

theorem rate_nonneg {n B : ℝ} (hn : 0 ≤ n) : 0 ≤ rate n B := by
  have hb0 := clippedDiameter_nonneg B
  unfold rate
  exact le_min (by positivity) (by positivity)

/-- With one component, the two candidates select the clipped diameter exactly. -/
theorem rate_one (B : ℝ) : rate 1 B = clippedDiameter B := by
  have hb : 0 ≤ clippedDiameter B ^ 4 := by positivity
  simp only [rate, Real.one_rpow, one_mul]
  exact min_eq_right (by linarith)

/-- For `B ≤ 1`, clipping removes all dependence on `B`. -/
theorem rate_of_diameter_le_one {n B : ℝ} (hB : B ≤ 1) :
    rate n B = min (n ^ (1 / 2 : ℝ) + 1) (n ^ (3 / 4 : ℝ)) := by
  simp [rate, clippedDiameter_of_le_one hB]

theorem rate_one_of_diameter_le_one {B : ℝ} (hB : B ≤ 1) : rate 1 B = 1 := by
  rw [rate_one, clippedDiameter_of_le_one hB]

/-- The first regime is within a factor two of `√n B̄`, including `B ≤ 1`. -/
theorem rate_small_regime {n B : ℝ} (hn : 1 ≤ n)
    (hB : B ≤ n ^ (1 / 6 : ℝ)) :
    n ^ (1 / 2 : ℝ) * clippedDiameter B ≤ rate n B ∧
      rate n B ≤ 2 * (n ^ (1 / 2 : ℝ) * clippedDiameter B) := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hb0 := clippedDiameter_nonneg B
  have hb : clippedDiameter B ≤ n ^ (1 / 6 : ℝ) :=
    max_le (Real.one_le_rpow hn (by norm_num)) hB
  have hc : clippedDiameter B ^ 3 ≤ n ^ (1 / 2 : ℝ) := by
    simpa only [sixth_cube hn0] using pow_le_pow_left₀ hb0 hb 3
  have h4 : clippedDiameter B ^ 4 ≤ n ^ (1 / 2 : ℝ) * clippedDiameter B := by
    have := mul_le_mul_of_nonneg_right hc hb0
    nlinarith only [this]
  have ht : n ^ (1 / 2 : ℝ) * clippedDiameter B ≤
      n ^ (3 / 4 : ℝ) * clippedDiameter B :=
    mul_le_mul_of_nonneg_right (half_le_three_quarters hn) hb0
  constructor
  · exact le_min (by linarith [show 0 ≤ clippedDiameter B ^ 4 by positivity]) ht
  · exact le_trans (min_le_left _ _) (by linarith)

/-- The intermediate regime is within a factor two of `B⁴`. -/
theorem rate_intermediate_regime {n B : ℝ} (hn : 1 ≤ n)
    (hBlo : n ^ (1 / 6 : ℝ) ≤ B) (hBhi : B ≤ n ^ (1 / 4 : ℝ)) :
    B ^ 4 ≤ rate n B ∧ rate n B ≤ 2 * B ^ 4 := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hB1 : 1 ≤ B := le_trans (Real.one_le_rpow hn (by norm_num)) hBlo
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB1
  have hlo : n ^ (1 / 2 : ℝ) ≤ B ^ 3 := by
    simpa only [sixth_cube hn0] using
      pow_le_pow_left₀ (Real.rpow_nonneg hn0 _) hBlo 3
  have hhi : B ^ 3 ≤ n ^ (3 / 4 : ℝ) := by
    simpa only [quarter_cube hn0] using pow_le_pow_left₀ hB0 hBhi 3
  have hp : 0 ≤ n ^ (1 / 2 : ℝ) * B := by positivity
  have hlo4 := mul_le_mul_of_nonneg_right hlo hB0
  have hhi4 := mul_le_mul_of_nonneg_right hhi hB0
  unfold rate
  rw [clippedDiameter_of_one_le hB1]
  constructor
  · exact le_min (by linarith) (by nlinarith only [hhi4])
  · refine le_trans (min_le_left _ _) ?_
    nlinarith only [hlo4]

/-- In the large-diameter regime the second candidate is the exact minimum. -/
theorem rate_large_regime {n B : ℝ} (hn : 1 ≤ n)
    (hB : n ^ (1 / 4 : ℝ) ≤ B) : rate n B = n ^ (3 / 4 : ℝ) * B := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hB1 : 1 ≤ B := le_trans (Real.one_le_rpow hn (by norm_num)) hB
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB1
  have hc : n ^ (3 / 4 : ℝ) ≤ B ^ 3 := by
    simpa only [quarter_cube hn0] using
      pow_le_pow_left₀ (Real.rpow_nonneg hn0 _) hB 3
  have hc4 := mul_le_mul_of_nonneg_right hc hB0
  have hp : 0 ≤ n ^ (1 / 2 : ℝ) * B := by positivity
  unfold rate
  rw [clippedDiameter_of_one_le hB1]
  exact min_eq_right (by nlinarith only [hc4, hp])

/-- In the large regime, the `n` term is absorbed by `n^(3/4) B`. -/
theorem large_regime_absorbs_full_pass {n B : ℝ} (hn : 1 ≤ n)
    (hB : n ^ (1 / 4 : ℝ) ≤ B) : n ≤ n ^ (3 / 4 : ℝ) * B := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  calc
    n = n ^ (3 / 4 : ℝ) * n ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hn0]
      norm_num
    _ ≤ n ^ (3 / 4 : ℝ) * B :=
      mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hn0.le _)

/-- Both complementary lower-bound coefficients are bounded by `𝓕`. -/
theorem complementary_lower_le_rate {n B : ℝ} (hn : 1 ≤ n) (hB : 0 ≤ B) :
    max (optimizationLower n B) (diameterLower n B) ≤ rate n B := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hb1 := clippedDiameter_one_le B
  have hb0 := clippedDiameter_nonneg B
  have hBB := le_clippedDiameter B
  have h4 : B ^ 4 ≤ clippedDiameter B ^ 4 := pow_le_pow_left₀ hB hBB 4
  have ht : n ^ (3 / 4 : ℝ) ≤ n ^ (3 / 4 : ℝ) * clippedDiameter B := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hb1 (Real.rpow_nonneg hn0 (3 / 4 : ℝ))
  have hp : 0 ≤ n ^ (1 / 2 : ℝ) * clippedDiameter B := by positivity
  unfold optimizationLower diameterLower rate
  apply max_le
  · exact le_min
      (le_trans (min_le_left _ _) (by linarith [show 0 ≤ clippedDiameter B ^ 4 by positivity]))
      (le_trans (min_le_right _ _) ht)
  · exact le_min
      (le_trans (min_le_left _ _) (by linarith))
      (le_trans (min_le_right _ _) (mul_le_mul_of_nonneg_left hBB (by positivity)))

/-- The max of the two mechanisms recovers `𝓕` within the explicit constant two.
This is the deterministic comparison used to combine (13) and (14). -/
theorem rate_le_twice_complementary_lower {n B : ℝ} (hn : 1 ≤ n) (hB : 0 ≤ B) :
    rate n B ≤ 2 * max (optimizationLower n B) (diameterLower n B) := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  by_cases hB1 : B ≤ 1
  · have hsmall : B ≤ n ^ (1 / 6 : ℝ) :=
      le_trans hB1 (Real.one_le_rpow hn (by norm_num))
    have hopt : optimizationLower n B = n ^ (1 / 2 : ℝ) := by
      simp only [optimizationLower, clippedDiameter_of_le_one hB1, mul_one]
      exact min_eq_left (half_le_three_quarters hn)
    have hr := (rate_small_regime hn hsmall).2
    rw [clippedDiameter_of_le_one hB1, mul_one] at hr
    have hm : n ^ (1 / 2 : ℝ) ≤ max (optimizationLower n B) (diameterLower n B) := by
      rw [← hopt]
      exact le_max_left _ _
    linarith
  · have hB1' : 1 ≤ B := le_of_lt (lt_of_not_ge hB1)
    by_cases hquarter : B ≤ n ^ (1 / 4 : ℝ)
    · have hopt : optimizationLower n B = n ^ (1 / 2 : ℝ) * B := by
        unfold optimizationLower
        rw [clippedDiameter_of_one_le hB1']
        apply min_eq_left
        calc
          n ^ (1 / 2 : ℝ) * B ≤ n ^ (1 / 2 : ℝ) * n ^ (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left hquarter (by positivity)
          _ = n ^ (3 / 4 : ℝ) := half_mul_quarter hnpos
      have hcube : B ^ 3 ≤ n ^ (3 / 4 : ℝ) := by
        simpa only [quarter_cube hn0] using pow_le_pow_left₀ hB hquarter 3
      have hdiam : diameterLower n B = B ^ 4 := by
        unfold diameterLower
        apply min_eq_left
        nlinarith only [mul_le_mul_of_nonneg_right hcube hB]
      have hm1 : n ^ (1 / 2 : ℝ) * B ≤
          max (optimizationLower n B) (diameterLower n B) := by
        rw [← hopt]
        exact le_max_left _ _
      have hm2 : B ^ 4 ≤ max (optimizationLower n B) (diameterLower n B) := by
        rw [← hdiam]
        exact le_max_right _ _
      refine le_trans (min_le_left _ _) ?_
      rw [clippedDiameter_of_one_le hB1']
      linarith
    · have hquarter' : n ^ (1 / 4 : ℝ) ≤ B := le_of_lt (lt_of_not_ge hquarter)
      have hcube : n ^ (3 / 4 : ℝ) ≤ B ^ 3 := by
        simpa only [quarter_cube hn0] using
          pow_le_pow_left₀ (Real.rpow_nonneg hn0 _) hquarter' 3
      have hdiam : diameterLower n B = n ^ (3 / 4 : ℝ) * B := by
        unfold diameterLower
        apply min_eq_right
        nlinarith only [mul_le_mul_of_nonneg_right hcube hB]
      rw [rate_large_regime hn hquarter']
      have hm : n ^ (3 / 4 : ℝ) * B ≤
          max (optimizationLower n B) (diameterLower n B) := by
        rw [← hdiam]
        exact le_max_right _ _
      have hp : 0 ≤ n ^ (3 / 4 : ℝ) * B := by positivity
      linarith

theorem complementary_lower_comparison {n B : ℝ} (hn : 1 ≤ n) (hB : 0 ≤ B) :
    max (optimizationLower n B) (diameterLower n B) ≤ rate n B ∧
    rate n B ≤ 2 * max (optimizationLower n B) (diameterLower n B) :=
  ⟨complementary_lower_le_rate hn hB, rate_le_twice_complementary_lower hn hB⟩

/-- Adding the full-pass cost `n` and multiplying by any `A ≥ 0` preserves the
factor-two comparison. This is the algebraic combination used in Theorem 3.1. -/
theorem full_cost_complementary_comparison {n A B : ℝ}
    (hn : 1 ≤ n) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    max (n + A * optimizationLower n B) (n + A * diameterLower n B) ≤
        n + A * rate n B ∧
      n + A * rate n B ≤
        2 * max (n + A * optimizationLower n B) (n + A * diameterLower n B) := by
  have hcoeff := complementary_lower_le_rate hn hB
  have hopt := (le_max_left (optimizationLower n B) (diameterLower n B)).trans hcoeff
  have hdiam := (le_max_right (optimizationLower n B) (diameterLower n B)).trans hcoeff
  constructor
  · apply max_le
    · linarith only [mul_le_mul_of_nonneg_left hopt hA]
    · linarith only [mul_le_mul_of_nonneg_left hdiam hA]
  · have hr := mul_le_mul_of_nonneg_left (rate_le_twice_complementary_lower hn hB) hA
    have hn0 : 0 ≤ n := le_trans (by norm_num) hn
    by_cases h : optimizationLower n B ≤ diameterLower n B
    · rw [max_eq_right h] at hr
      have hm := le_max_right (n + A * optimizationLower n B) (n + A * diameterLower n B)
      nlinarith only [hr, hn0, hm]
    · have h' : diameterLower n B ≤ optimizationLower n B := le_of_lt (lt_of_not_ge h)
      rw [max_eq_left h'] at hr
      have hm := le_max_left (n + A * optimizationLower n B) (n + A * diameterLower n B)
      nlinarith only [hr, hn0, hm]

end

end NCConcave16991
