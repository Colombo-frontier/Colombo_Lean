import LowRank.RitzSchattenSpectrum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Real-power deficit bounds for Ritz values. The same inequality covers
exponents below and above one, including every finite positive Schatten
parameter, with an explicit coefficient instead of asymptotic notation. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem rpow_unit_interval_lower {z r : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - max 1 r * (1 - z) ≤ z ^ r := by
  by_cases hr : r ≤ 1
  · rw [max_eq_left hr]
    simpa only [one_mul, sub_sub_cancel] using Real.self_le_rpow_of_le_one hz hz1 hr
  · have hr1 : 1 ≤ r := le_of_not_ge hr
    have h := one_add_mul_self_le_rpow_one_add (s := z - 1) (by linarith) hr1
    rw [max_eq_right hr1]
    convert h using 1 <;> congr 1 <;> ring

theorem rpow_loss_le {x y r : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x) :
    x ^ r - y ^ r ≤ max 1 r * (x - y) * x ^ (r - 1) := by
  have hz : 0 ≤ y / x := div_nonneg hy hx.le
  have hz1 : y / x ≤ 1 := (div_le_one hx).mpr hyx
  have h := mul_le_mul_of_nonneg_left (rpow_unit_interval_lower (r := r) hz hz1)
    (Real.rpow_nonneg hx.le r)
  have he : x ^ r * (y / x) ^ r = y ^ r := by
    rw [← Real.mul_rpow hx.le hz, mul_div_cancel₀ _ (ne_of_gt hx)]
  rw [he] at h
  have halg : x ^ r * (1 - max 1 r * (1 - y / x)) =
      x ^ r - max 1 r * (x - y) * x ^ (r - 1) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp
    ring
  rw [halg] at h
  linarith

theorem rpow_lower_of_additive_error {x y r e : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hr : 0 ≤ r) (he : 0 ≤ e) (hxy : x - e ≤ y) :
    x ^ r - max 1 r * e * x ^ (r - 1) ≤ y ^ r := by
  have hc : 0 ≤ max 1 r := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  by_cases hyx : y ≤ x
  · have hl := rpow_loss_le hx hy hyx (r := r)
    have hdiff : x - y ≤ e := by linarith
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff hc)
      (Real.rpow_nonneg hx.le (r - 1))
    linarith
  · have hpow := Real.rpow_le_rpow hx.le (le_of_not_ge hyx) hr
    have hn := mul_nonneg (mul_nonneg hc he) (Real.rpow_nonneg hx.le (r - 1))
    linarith

theorem rpow_lower_of_additive_error_of_nonneg {x y r e : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hr : 0 < r) (he : 0 ≤ e) (hxy : x - e ≤ y) :
    x ^ r - max 1 r * e * x ^ (r - 1) ≤ y ^ r := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0, Real.zero_rpow (ne_of_gt hr), zero_sub]
    exact (neg_nonpos.mpr (mul_nonneg (mul_nonneg
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) he)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0) _))).trans (Real.rpow_nonneg hy r)
  · exact rpow_lower_of_additive_error hx0 hy hr.le he hxy

theorem optimalColumnSelector_power_deficit {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {p : ℝ} (hp : 0 < p)
    (x e : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j) (he : ∀ j, 0 ≤ e j)
    (happrox : ∀ j, x j - e j ≤ (canonicalOrderedSpectrum b (symmetricRightGram A)).value
      (lastColumnIndex b k hk j)) :
    (∑ j, x j ^ (p / 2)) - (∑ j, max 1 (p / 2) * e j * x j ^ (p / 2 - 1)) ≤
      schattenPower p (A * optimalColumnSelector a b k hk A) := by
  rw [optimalColumnSelector_schattenPower, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact rpow_lower_of_additive_error_of_nonneg (hx j)
    ((canonicalOrderedSpectrum b (symmetricRightGram A)).value_nonneg (rightGram_posSemidef A) _)
    (by positivity) (he j) (happrox j)

theorem compressedRitz_power_deficit {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (P : Matrix (Fin b) (Fin b) ℝ)
    (hfix : P * optimalColumnSelector a b k hk (A * P) = optimalColumnSelector a b k hk (A * P))
    {p : ℝ} (hp : 0 < p) (x e : Fin k → ℝ) (hx : ∀ j, 0 < x j) (he : ∀ j, 0 ≤ e j)
    (happrox : ∀ j, x j - e j ≤ (canonicalOrderedSpectrum b (symmetricRightGram (A * P))).value
      (lastColumnIndex b k hk j)) :
    (∑ j, x j ^ (p / 2)) - (∑ j, max 1 (p / 2) * e j * x j ^ (p / 2 - 1)) ≤
      schattenPower p (A * optimalColumnSelector a b k hk (A * P)) := by
  have h := optimalColumnSelector_power_deficit hk (A * P) hp x e (fun j => (hx j).le) he happrox
  rwa [Matrix.mul_assoc, hfix] at h

end
end LowRank
