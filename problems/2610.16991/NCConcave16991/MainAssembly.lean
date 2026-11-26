import NCConcave16991.Rates
import Mathlib.Basic.ENNReal.Real

/-!
# The numerical assembly used in Appendix F.3

The oracle upper and lower constructions are inputs here, not conclusions of
the rate calculations. This file proves the remaining combination with
explicit constants, for possibly infinite complexity.
-/

namespace NCConcave16991

open scoped ENNReal

noncomputable section

def averagingWork (n A B : ℝ) : ℝ :=
  n + (1 + A) * (n ^ (1 / 2 : ℝ) * clippedDiameter B + clippedDiameter B ^ 4)

def acceleratedWork (n A B ell : ℝ) : ℝ :=
  (1 + A) * (n + n ^ (3 / 4 : ℝ) * B) * ell

theorem averaging_coefficient_le_twice_rate {n B : ℝ} (hn : 1 ≤ n)
    (hB : B ≤ n ^ (1 / 4 : ℝ)) :
    n ^ (1 / 2 : ℝ) * clippedDiameter B + clippedDiameter B ^ 4 ≤ 2 * rate n B := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hb0 := clippedDiameter_nonneg B
  have hb : clippedDiameter B ≤ n ^ (1 / 4 : ℝ) :=
    max_le (Real.one_le_rpow hn (by norm_num)) hB
  have hcube : (n ^ (1 / 4 : ℝ)) ^ (3 : ℕ) = n ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  have hc : clippedDiameter B ^ 3 ≤ n ^ (3 / 4 : ℝ) := by
    simpa only [hcube] using pow_le_pow_left₀ hb0 hb 3
  have hfour : clippedDiameter B ^ 4 ≤ n ^ (3 / 4 : ℝ) * clippedDiameter B := by
    nlinarith only [mul_le_mul_of_nonneg_right hc hb0]
  have hhalf := mul_le_mul_of_nonneg_right (half_le_three_quarters hn) hb0
  unfold rate
  rw [mul_min_of_nonneg _ _ (show 0 ≤ (2 : ℝ) by norm_num)]
  apply le_min
  · have hnonneg : 0 ≤ n ^ (1 / 2 : ℝ) * clippedDiameter B + clippedDiameter B ^ 4 := by positivity
    linarith
  · linarith

theorem small_diameter_work_bound {n A B ell : ℝ}
    (hn : 1 ≤ n) (hA : 1 ≤ A) (hell : 1 ≤ ell)
    (hB : B ≤ n ^ (1 / 4 : ℝ)) :
    averagingWork n A B ≤ 4 * (n + A * rate n B) * ell := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hr0 := rate_nonneg (B := B) hn0
  have hw := averaging_coefficient_le_twice_rate hn hB
  have hwork : 0 ≤ n ^ (1 / 2 : ℝ) * clippedDiameter B + clippedDiameter B ^ 4 := by
    have hh := clippedDiameter_nonneg B
    positivity
  have h1 := mul_le_mul_of_nonneg_right (show 1 + A ≤ 2 * A by linarith) hwork
  have h2 := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 * A by positivity)
  have h3 := mul_le_mul_of_nonneg_left hell (show 0 ≤ 4 * (n + A * rate n B) by positivity)
  dsimp [averagingWork]
  nlinarith

theorem large_diameter_work_bound {n A B ell : ℝ}
    (hn : 1 ≤ n) (hA : 1 ≤ A) (hell : 0 ≤ ell)
    (hB : n ^ (1 / 4 : ℝ) ≤ B) :
    acceleratedWork n A B ell ≤ 4 * (n + A * rate n B) * ell := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hBn := large_regime_absorbs_full_pass hn hB
  rw [rate_large_regime hn hB]
  have hB0 : 0 ≤ B := (Real.rpow_nonneg hn0 _).trans hB
  have ht : 0 ≤ n ^ (3 / 4 : ℝ) * B := by positivity
  have h1 := mul_le_mul_of_nonneg_right (show 1 + A ≤ 2 * A by linarith)
    (show 0 ≤ n + n ^ (3 / 4 : ℝ) * B by positivity)
  have h2 := mul_le_mul_of_nonneg_left hBn hA0
  apply mul_le_mul_of_nonneg_right _ hell
  nlinarith

theorem matching_upper_work {n A B ell : ℝ}
    (hn : 1 ≤ n) (hA : 1 ≤ A) (hell : 1 ≤ ell) :
    min (averagingWork n A B) (acceleratedWork n A B ell) ≤
      4 * (n + A * rate n B) * ell := by
  by_cases hB : B ≤ n ^ (1 / 4 : ℝ)
  · exact (min_le_left _ _).trans (small_diameter_work_bound hn hA hell hB)
  · exact (min_le_right _ _).trans
      (large_diameter_work_bound hn hA (by linarith) (le_of_not_ge hB))

/-- The exact conditional sandwich: proving its four input oracle bounds is
the substantive remaining task of Theorems 3.2 and 3.3. -/
theorem matching_sandwich_of_complementary_bounds
    {n A B ell c C : ℝ} {T : ℝ≥0∞}
    (hn : 1 ≤ n) (hA : 1 ≤ A) (hB : 0 ≤ B) (hell : 1 ≤ ell)
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hl1 : ENNReal.ofReal (c * (n + A * optimizationLower n B)) ≤ T)
    (hl2 : ENNReal.ofReal (c * (n + A * diameterLower n B)) ≤ T)
    (hu1 : T ≤ ENNReal.ofReal (C * averagingWork n A B))
    (hu2 : T ≤ ENNReal.ofReal (C * acceleratedWork n A B ell)) :
    ENNReal.ofReal ((c / 2) * (n + A * rate n B)) ≤ T ∧
      T ≤ ENNReal.ofReal (4 * C * (n + A * rate n B) * ell) := by
  constructor
  · have hh := (full_cost_complementary_comparison hn (by linarith : 0 ≤ A) hB).2
    by_cases h : n + A * optimizationLower n B ≤ n + A * diameterLower n B
    · rw [max_eq_right h] at hh
      apply le_trans (ENNReal.ofReal_le_ofReal ?_) hl2
      nlinarith [mul_le_mul_of_nonneg_left hh hc]
    · rw [max_eq_left (le_of_not_ge h)] at hh
      apply le_trans (ENNReal.ofReal_le_ofReal ?_) hl1
      nlinarith [mul_le_mul_of_nonneg_left hh hc]
  · have hmin : T ≤ ENNReal.ofReal (C * min (averagingWork n A B) (acceleratedWork n A B ell)) := by
      by_cases h : averagingWork n A B ≤ acceleratedWork n A B ell
      · simpa only [min_eq_left h] using hu1
      · simpa only [min_eq_right (le_of_not_ge h)] using hu2
    apply hmin.trans (ENNReal.ofReal_le_ofReal ?_)
    have hh := mul_le_mul_of_nonneg_left (matching_upper_work (B := B) hn hA hell) hC
    nlinarith

end

end NCConcave16991
