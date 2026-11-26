import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! Quantitative Chebyshev estimates used for Krylov filtering. The
polynomial is bounded on [-1,1] and grows exponentially beyond 1+gamma,
with exponent proportional to the square root of the gap. -/

namespace LowRank
open Polynomial
noncomputable section

def chebyshevAngle (x : ℝ) : ℝ := Real.log (x + Real.sqrt (x ^ 2 - 1))

theorem chebyshevAngle_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ chebyshevAngle x := by
  apply Real.log_nonneg
  linarith [Real.sqrt_nonneg (x ^ 2 - 1)]

theorem cosh_chebyshevAngle {x : ℝ} (hx : 1 ≤ x) : Real.cosh (chebyshevAngle x) = x := by
  have hs : 0 ≤ x ^ 2 - 1 := by nlinarith
  have hsq := Real.sq_sqrt hs
  have hp : 0 < x + Real.sqrt (x ^ 2 - 1) := by linarith [Real.sqrt_nonneg (x ^ 2 - 1)]
  have hi : (x + Real.sqrt (x ^ 2 - 1))⁻¹ = x - Real.sqrt (x ^ 2 - 1) :=
    inv_eq_of_mul_eq_one_right (by nlinarith)
  rw [chebyshevAngle, Real.cosh_log hp, hi]
  ring

theorem chebyshevAngle_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    chebyshevAngle x ≤ chebyshevAngle y := by
  apply Real.log_le_log
  · linarith [Real.sqrt_nonneg (x ^ 2 - 1)]
  · have hs : x ^ 2 - 1 ≤ y ^ 2 - 1 := by nlinarith
    exact add_le_add hxy (Real.sqrt_le_sqrt hs)

theorem chebyshev_eval_cosh (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (Chebyshev.T ℝ (n : ℤ)).eval x = Real.cosh ((n : ℝ) * chebyshevAngle x) := by
  have h := Chebyshev.T_real_cosh (chebyshevAngle x) (n : ℤ)
  simpa only [cosh_chebyshevAngle hx, Int.cast_natCast] using h

theorem chebyshev_eval_ge_one (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ (Chebyshev.T ℝ (n : ℤ)).eval x := by
  rw [chebyshev_eval_cosh n hx]
  exact Real.one_le_cosh _

theorem chebyshev_eval_mono (n : ℕ) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (Chebyshev.T ℝ (n : ℤ)).eval x ≤ (Chebyshev.T ℝ (n : ℤ)).eval y := by
  rw [chebyshev_eval_cosh n hx, chebyshev_eval_cosh n (hx.trans hxy)]
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (chebyshevAngle_nonneg hx)),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (chebyshevAngle_nonneg (hx.trans hxy)))]
  exact mul_le_mul_of_nonneg_left (chebyshevAngle_mono hx hxy) (Nat.cast_nonneg n)

theorem chebyshev_eval_abs_le_one (n : ℕ) {x : ℝ} (hl : -1 ≤ x) (hu : x ≤ 1) :
    |(Chebyshev.T ℝ (n : ℤ)).eval x| ≤ 1 := by
  have h := Chebyshev.T_real_cos (Real.arccos x) (n : ℤ)
  rw [Real.cos_arccos hl hu] at h
  rw [h]
  exact Real.abs_cos_le_one _

theorem chebyshevAngle_ge_sqrt_half {γ x : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hx : 1 + γ ≤ x) : Real.sqrt γ / 2 ≤ chebyshevAngle x := by
  have ht := Real.sqrt_nonneg γ
  have ht1 : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr hγ1
  have hsq : γ ≤ x ^ 2 - 1 := by nlinarith
  have hs := Real.sqrt_le_sqrt hsq
  have hlog : Real.sqrt γ / 2 ≤ Real.log (1 + Real.sqrt γ) := by
    apply le_trans _ (Real.le_log_one_add_of_nonneg ht)
    apply (le_div_iff₀ (by positivity : 0 < Real.sqrt γ + 2)).mpr
    nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
  exact hlog.trans (Real.log_le_log (by positivity) (by linarith))

theorem chebyshev_eval_gap_growth (n : ℕ) {γ x : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hx : 1 + γ ≤ x) :
    Real.exp ((n : ℝ) * Real.sqrt γ / 2) / 2 ≤ (Chebyshev.T ℝ (n : ℤ)).eval x := by
  rw [chebyshev_eval_cosh n (by linarith : 1 ≤ x), Real.cosh_eq]
  have he : Real.exp ((n : ℝ) * Real.sqrt γ / 2) ≤
      Real.exp ((n : ℝ) * chebyshevAngle x) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (chebyshevAngle_ge_sqrt_half hγ hγ1 hx)
      (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)
    nlinarith
  linarith [Real.exp_pos (-((n : ℝ) * chebyshevAngle x))]

theorem chebyshev_eval_gap_ratio (n : ℕ) {γ x y : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hxl : -1 ≤ x) (hxu : x ≤ 1) (hy : 1 + γ ≤ y) :
    |(Chebyshev.T ℝ (n : ℤ)).eval x / (Chebyshev.T ℝ (n : ℤ)).eval y| ≤
      2 * Real.exp (-((n : ℝ) * Real.sqrt γ / 2)) := by
  have hd := chebyshev_eval_gap_growth n hγ hγ1 hy
  have hden : 0 < (Chebyshev.T ℝ (n : ℤ)).eval y :=
    lt_of_lt_of_le (by positivity) hd
  rw [abs_div, abs_of_pos hden]
  calc
    _ ≤ 1 / (Real.exp ((n : ℝ) * Real.sqrt γ / 2) / 2) :=
      div_le_div₀ (by norm_num) (chebyshev_eval_abs_le_one n hxl hxu) (by positivity) hd
    _ = 2 * Real.exp (-((n : ℝ) * Real.sqrt γ / 2)) := by
      rw [Real.exp_neg]
      ring

theorem chebyshev_natDegree_le (n : ℕ) : (Chebyshev.T ℝ (n : ℤ)).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih1 =>
      rw [Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two]
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · have hmul := natDegree_mul_le (p := (2 : ℝ[X]) * X) (q := Chebyshev.T ℝ ((n : ℤ) + 1))
        have hdeg : ((2 : ℝ[X]) * X).natDegree ≤ 1 := by
          simpa using (natDegree_mul_le (p := (2 : ℝ[X])) (q := X))
        have hi : (Chebyshev.T ℝ ((n : ℤ) + 1)).natDegree ≤ n + 1 := by
          simpa only [Nat.cast_add, Nat.cast_one] using ih1
        omega
      · omega

end
end LowRank
