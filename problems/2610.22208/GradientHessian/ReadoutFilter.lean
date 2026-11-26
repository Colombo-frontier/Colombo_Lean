import LowRank.ChebyshevGapFilter
import Mathlib.Tactic

/-! The literal Chebyshev filter and degree in the manuscript. The sharper
angle bound is proved with the source constants, without increasing its degree. -/

namespace GradientHessian.ReadoutFilter

open Polynomial LowRank
noncomputable section

def delta : ℝ := min ((1 / 3072) / 32) (1 / 1000)
def degree (M tolerance : ℝ) : ℕ := ⌈Real.sqrt M / 2 * Real.log (2 / tolerance)⌉₊
def base (M : ℝ) : ℝ := (M + 3) / (M - 5)
def argument (M t : ℝ) : ℝ := (M + 5 - 2 * t) / (M - 5)

def filterPolynomial (M tolerance : ℝ) : ℝ[X] :=
  (chebyshevGapFilter (M - 5) (8 / (M - 5)) (degree M tolerance)).comp (C M - X)

theorem delta_eq : delta = 1 / 98304 := by norm_num [delta]
theorem delta_pos : 0 < delta := by rw [delta_eq]; norm_num
theorem delta_le_thousandth : delta ≤ 1 / 1000 := min_le_right _ _
theorem delta_le_one : delta ≤ 1 := delta_le_thousandth.trans (by norm_num)

theorem base_ge_one {M : ℝ} (hM : 5 < M) : 1 ≤ base M := by
  rw [base, le_div_iff₀ (by linarith : 0 < M - 5)]
  linarith

theorem base_angle_bound {M : ℝ} (hM : 16 ≤ M) :
    2 / Real.sqrt M ≤ chebyshevAngle (base M) := by
  have hM0 : 0 < M := by linarith
  have hM5 : 0 < M - 5 := by linarith
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  have hs4 : 4 ≤ Real.sqrt M := Real.le_sqrt_of_sq_le (by nlinarith)
  have hb : 1 ≤ base M := base_ge_one (by linarith)
  have hsq : 16 / M ≤ (base M) ^ 2 - 1 := by
    calc
      16 / M ≤ ((M + 3) ^ 2 - (M - 5) ^ 2) / (M - 5) ^ 2 := by
        apply (div_le_div_iff₀ hM0 (sq_pos_of_pos hM5)).mpr
        nlinarith
      _ = (base M) ^ 2 - 1 := by
        unfold base
        field_simp
  have hroot : 4 / Real.sqrt M ≤ Real.sqrt ((base M) ^ 2 - 1) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [div_pow, Real.sq_sqrt hM0.le, show (4 : ℝ)^2 = 16 by norm_num] using hsq
  have hx0 : 0 ≤ 4 / Real.sqrt M := by positivity
  have hx1 : 4 / Real.sqrt M ≤ 1 := (div_le_one hs).mpr hs4
  have hlog : 2 / Real.sqrt M ≤ Real.log (1 + 4 / Real.sqrt M) := by
    have h := Real.le_log_one_add_of_nonneg hx0
    have hh : (4 / Real.sqrt M) / 2 ≤
        2 * (4 / Real.sqrt M) / (4 / Real.sqrt M + 2) := by
      apply (le_div_iff₀ (by positivity : 0 < 4 / Real.sqrt M + 2)).mpr
      nlinarith
    calc
      2 / Real.sqrt M = (4 / Real.sqrt M) / 2 := by ring
      _ ≤ _ := hh.trans h
  exact hlog.trans (Real.log_le_log (by positivity) (by linarith))

theorem denominator_growth (n : ℕ) {M : ℝ} (hM : 16 ≤ M) :
    Real.exp (2 * (n : ℝ) / Real.sqrt M) / 2 ≤
      (Chebyshev.T ℝ (n : ℤ)).eval (base M) := by
  rw [chebyshev_eval_cosh n (base_ge_one (by linarith)), Real.cosh_eq]
  have h := mul_le_mul_of_nonneg_left (base_angle_bound hM) (Nat.cast_nonneg n)
  have he : Real.exp (2 * (n : ℝ) / Real.sqrt M) ≤
      Real.exp ((n : ℝ) * chebyshevAngle (base M)) :=
    Real.exp_le_exp.mpr (by convert h using 1; ring)
  linarith [Real.exp_pos (-((n : ℝ) * chebyshevAngle (base M)))]

theorem degree_exponent {M tolerance : ℝ} (hM : 0 < M) :
    Real.log (2 / tolerance) ≤ 2 * (degree M tolerance : ℝ) / Real.sqrt M := by
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have h := Nat.le_ceil (Real.sqrt M / 2 * Real.log (2 / tolerance))
  apply (le_div_iff₀ hs).mpr
  change Real.sqrt M / 2 * Real.log (2 / tolerance) ≤ (degree M tolerance : ℝ) at h
  nlinarith

theorem denominator_lower {M tolerance : ℝ} (hM : 16 ≤ M) (ht : 0 < tolerance) :
    1 / tolerance ≤ (Chebyshev.T ℝ (degree M tolerance : ℤ)).eval (base M) := by
  have he : Real.exp (Real.log (2 / tolerance)) ≤
      Real.exp (2 * (degree M tolerance : ℝ) / Real.sqrt M) :=
    Real.exp_le_exp.mpr (degree_exponent (by linarith))
  rw [Real.exp_log (by positivity)] at he
  have hg := denominator_growth (degree M tolerance) hM
  calc
    1 / tolerance = (2 / tolerance) / 2 := by ring
    _ ≤ Real.exp (2 * (degree M tolerance : ℝ) / Real.sqrt M) / 2 :=
      div_le_div_of_nonneg_right he (by norm_num)
    _ ≤ _ := hg

theorem filterPolynomial_eval {M tolerance t : ℝ} (hM : 5 < M) :
    (filterPolynomial M tolerance).eval t =
      (Chebyshev.T ℝ (degree M tolerance : ℤ)).eval (argument M t) /
        (Chebyshev.T ℝ (degree M tolerance : ℤ)).eval (base M) := by
  rw [filterPolynomial, eval_comp]
  simp only [eval_sub, eval_C, eval_X]
  rw [chebyshevGapFilter_eval]
  have hd : M - 5 ≠ 0 := by linarith
  have hnum : 2 * (M - t) / (M - 5) - 1 = argument M t := by
    unfold argument
    field_simp
    ring
  have hden : 1 + 8 / (M - 5) = base M := by
    unfold base
    field_simp
    ring
  rw [hnum, hden]

theorem filterPolynomial_natDegree_le (M tolerance : ℝ) :
    (filterPolynomial M tolerance).natDegree ≤ degree M tolerance := by
  apply natDegree_comp_le.trans
  have hlin : (C M - (X : ℝ[X])).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  calc
    _ ≤ degree M tolerance * 1 :=
      Nat.mul_le_mul (chebyshevGapFilter_natDegree_le _ _ _) hlin
    _ = degree M tolerance := Nat.mul_one _

theorem filterPolynomial_one {M tolerance : ℝ} (hM : 5 < M) :
    (filterPolynomial M tolerance).eval 1 = 1 := by
  rw [filterPolynomial_eval hM]
  have ha : argument M 1 = base M := by unfold argument base; congr 1; ring
  rw [ha]
  exact div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one
    (chebyshev_eval_ge_one _ (base_ge_one hM))))

theorem filterPolynomial_tail {M tolerance t : ℝ} (hM : 16 ≤ M)
    (htol : 0 < tolerance) (ht5 : 5 ≤ t) (htM : t ≤ M) :
    |(filterPolynomial M tolerance).eval t| ≤ tolerance := by
  rw [filterPolynomial_eval (by linarith)]
  have hd : 0 < M - 5 := by linarith
  have ha1 : -1 ≤ argument M t := by
    rw [argument, le_div_iff₀ hd]
    linarith
  have ha2 : argument M t ≤ 1 := by
    rw [argument, div_le_iff₀ hd]
    linarith
  have hden := denominator_lower hM htol
  have hp : 0 < (Chebyshev.T ℝ (degree M tolerance : ℤ)).eval (base M) :=
    lt_of_lt_of_le (by positivity) hden
  rw [abs_div, abs_of_pos hp]
  calc
    _ ≤ 1 / (1 / tolerance) :=
      div_le_div₀ (by norm_num) (chebyshev_eval_abs_le_one _ ha1 ha2) (by positivity) hden
    _ = tolerance := by field_simp

def matrixUpper (J : ℕ) : ℝ := 1 + 4096 * (J : ℝ) ^ 2
def degreeConstant : ℝ := 65 / 2 * Real.log (2 / delta) + 1

theorem matrixUpper_sqrt_le {J : ℕ} (hJ : 1 ≤ J) :
    Real.sqrt (matrixUpper J) ≤ 65 * (J : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  have hJr : 1 ≤ (J : ℝ) := by exact_mod_cast hJ
  constructor
  · positivity
  · unfold matrixUpper
    nlinarith [sq_nonneg ((J : ℝ) - 1)]

theorem degreeConstant_pos : 0 < degreeConstant := by
  have hlog : 0 ≤ Real.log (2 / delta) := Real.log_nonneg
    ((le_div_iff₀ delta_pos).mpr (by linarith [delta_le_one]))
  unfold degreeConstant
  positivity

/-- The exact degree chosen in the article is bounded by one absolute
constant times J; no larger polynomial degree is substituted. -/
theorem degree_linear_bound {J : ℕ} (hJ : 1 ≤ J) :
    (degree (matrixUpper J) delta : ℝ) ≤ degreeConstant * J := by
  have hJr : 1 ≤ (J : ℝ) := by exact_mod_cast hJ
  have hlog : 0 ≤ Real.log (2 / delta) := Real.log_nonneg
    ((le_div_iff₀ delta_pos).mpr (by linarith [delta_le_one]))
  have hc : (degree (matrixUpper J) delta : ℝ) <
      Real.sqrt (matrixUpper J) / 2 * Real.log (2 / delta) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hs := mul_le_mul_of_nonneg_right (matrixUpper_sqrt_le hJ) hlog
  unfold degreeConstant
  nlinarith

end
end GradientHessian.ReadoutFilter
