import SampleReuse.Model
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! The exact flat exponential gate in the manuscript's deterministic
curvature chain, including its first and second derivatives at the boundary. -/

namespace SampleReuse
noncomputable section

def glueFirst (t : ℝ) : ℝ := t⁻¹^2*expNegInvGlue t
def glueSecond (t : ℝ) : ℝ := (t⁻¹^4-2*t⁻¹^3)*expNegInvGlue t

theorem glue_hasDerivAt (t : ℝ) : HasDerivAt expNegInvGlue (glueFirst t) t := by
  simpa [glueFirst] using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 t

theorem glueFirst_hasDerivAt (t : ℝ) : HasDerivAt glueFirst (glueSecond t) t := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    (Polynomial.X^2 : Polynomial ℝ) t
  have he : ((Polynomial.X^2 * ((Polynomial.X^2 : Polynomial ℝ) -
      Polynomial.derivative (Polynomial.X^2))).eval t⁻¹ * expNegInvGlue t) =
      glueSecond t := by
    simp only [Polynomial.derivative_pow, Polynomial.derivative_X, mul_one,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_natCast, Polynomial.eval_C, Polynomial.eval_one]
    unfold glueSecond
    ring
  rw [he] at h
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using h

def curvatureGate (u : ℝ) : ℝ := expNegInvGlue (u-1/2)+expNegInvGlue (-u-1/2)
def curvatureGateFirst (u : ℝ) : ℝ := glueFirst (u-1/2)-glueFirst (-u-1/2)
def curvatureGateSecond (u : ℝ) : ℝ := glueSecond (u-1/2)+glueSecond (-u-1/2)

theorem curvatureGate_contDiff (n : ℕ∞) : ContDiff ℝ n curvatureGate :=
  (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).add
    (expNegInvGlue.contDiff.comp (contDiff_id.neg.sub contDiff_const))

theorem curvatureGate_hasDerivAt (u : ℝ) :
    HasDerivAt curvatureGate (curvatureGateFirst u) u := by
  simpa only [mul_one, mul_neg_one, sub_eq_add_neg, curvatureGate, curvatureGateFirst,
    Function.comp_def] using
    ((glue_hasDerivAt (u-1/2)).comp u ((hasDerivAt_id u).sub_const (1/2))).add
      ((glue_hasDerivAt (-u-1/2)).comp u ((hasDerivAt_id u).neg.sub_const (1/2)))

theorem curvatureGateFirst_hasDerivAt (u : ℝ) :
    HasDerivAt curvatureGateFirst (curvatureGateSecond u) u := by
  simpa only [mul_one, mul_neg_one, sub_neg_eq_add, curvatureGateFirst, curvatureGateSecond,
    Function.comp_def] using
    ((glueFirst_hasDerivAt (u-1/2)).comp u ((hasDerivAt_id u).sub_const (1/2))).sub
      ((glueFirst_hasDerivAt (-u-1/2)).comp u ((hasDerivAt_id u).neg.sub_const (1/2)))

theorem curvatureGate_deriv : deriv curvatureGate = curvatureGateFirst :=
  funext (fun u => (curvatureGate_hasDerivAt u).deriv)

theorem curvatureGate_second_deriv : deriv (deriv curvatureGate) = curvatureGateSecond := by
  rw [curvatureGate_deriv]
  exact funext (fun u => (curvatureGateFirst_hasDerivAt u).deriv)

theorem curvatureGate_flat {u : ℝ} (hu : |u| ≤ 1/2) :
    curvatureGate u = 0 ∧ deriv curvatureGate u = 0 ∧ deriv (deriv curvatureGate) u = 0 := by
  have hp : u-1/2 ≤ 0 := by linarith [(abs_le.mp hu).2]
  have hn : -u-1/2 ≤ 0 := by linarith [(abs_le.mp hu).1]
  rw [curvatureGate_second_deriv, curvatureGate_deriv]
  simp only [curvatureGate,
    curvatureGateFirst, curvatureGateSecond, glueFirst, glueSecond,
    expNegInvGlue.zero_of_nonpos hp, expNegInvGlue.zero_of_nonpos hn,
    mul_zero, zero_add, sub_self, and_self]

theorem glueSecond_nonneg {t : ℝ} (ht : t ≤ 1/2) : 0 ≤ glueSecond t := by
  by_cases hp : t ≤ 0
  · simp [glueSecond, expNegInvGlue.zero_of_nonpos hp]
  · have hpos : 0 < t := lt_of_not_ge hp
    have hinv : 2 ≤ t⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hpos).mpr
      linarith
    have hpoly : 0 ≤ t⁻¹^4-2*t⁻¹^3 := by
      have hh := mul_nonneg (pow_nonneg (inv_nonneg.mpr hpos.le) 3) (sub_nonneg.mpr hinv)
      nlinarith only [hh]
    exact mul_nonneg hpoly (expNegInvGlue.nonneg _)

theorem curvatureGate_convex_region {u : ℝ} (hu : |u| ≤ 1) :
    0 ≤ deriv (deriv curvatureGate) u := by
  rw [curvatureGate_second_deriv]
  exact add_nonneg (glueSecond_nonneg (by linarith [(abs_le.mp hu).2]))
    (glueSecond_nonneg (by linarith [(abs_le.mp hu).1]))

theorem curvatureGate_nonneg (u : ℝ) : 0 ≤ curvatureGate u :=
  add_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

theorem curvatureGate_one : curvatureGate 1 = Real.exp (-2) := by
  norm_num [curvatureGate, expNegInvGlue]

end
end SampleReuse
