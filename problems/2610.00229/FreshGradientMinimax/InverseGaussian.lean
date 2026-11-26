import FreshGradientMinimax.CoreTheta
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Smoothness at the flat threshold of the one-sided inverse Gaussian.
The polynomial closure argument also provides all derivatives of the gate's
square root, without differentiating a square root at its zero set. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open Polynomial Real Filter Set Function
open scoped Topology

def inverseGaussian (a x : ℝ) : ℝ := if x ≤ 0 then 0 else exp (-a * x⁻¹ ^ 2)

theorem inverseGaussian_nonpos (a : ℝ) {x : ℝ} (hx : x ≤ 0) : inverseGaussian a x = 0 := by
  rw [inverseGaussian, if_pos hx]

theorem inverseGaussian_zero (a : ℝ) : inverseGaussian a 0 = 0 := inverseGaussian_nonpos a le_rfl

theorem inverseGaussian_nonneg (a x : ℝ) : 0 ≤ inverseGaussian a x := by
  unfold inverseGaussian
  split_ifs
  · rfl
  · exact (exp_pos _).le

theorem polynomial_gaussian_tendsto {a : ℝ} (ha : 0 < a) (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * exp (-a * x ^ 2)) atTop (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => exp (-(1 / 2) * x)) atTop (𝓝 0) := by
    convert tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)) using 1
    funext x
    simp only [Function.comp_def, id_eq]
    congr 1
    ring
  induction p using Polynomial.induction_on' with
  | monomial n c =>
    have hn : Tendsto (fun x : ℝ => x ^ n * exp (-a * x ^ 2)) atTop (𝓝 0) := by
      simpa only [Real.rpow_natCast] using
        (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg ha (n : ℝ)).tendsto_zero_of_tendsto he
    simpa only [eval_monomial, mul_assoc, mul_zero] using tendsto_const_nhds.mul hn
  | add p q hp hq => simpa only [eval_add, add_mul, add_zero] using hp.add hq

theorem inverseGaussian_polynomial_limit {a : ℝ} (ha : 0 < a) (p : ℝ[X]) :
    Tendsto (fun x => p.eval x⁻¹ * inverseGaussian a x) (𝓝 0) (𝓝 0) := by
  simp only [inverseGaussian, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  exact (polynomial_gaussian_tendsto ha p).comp tendsto_inv_nhdsGT_zero

def inverseGaussianNext (a : ℝ) (p : ℝ[X]) : ℝ[X] := C (2 * a) * X ^ 3 * p - X ^ 2 * derivative p

theorem inverseGaussian_polynomial_hasDerivAt {a : ℝ} (ha : 0 < a) (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x => p.eval x⁻¹ * inverseGaussian a x)
      ((inverseGaussianNext a p).eval x⁻¹ * inverseGaussian a x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [inverseGaussian_nonpos a hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    rw [inverseGaussian_nonpos a hy.le, mul_zero]
  · rw [inverseGaussian_zero, mul_zero, hasDerivAt_iff_tendsto_slope]
    refine ((inverseGaussian_polynomial_limit ha (p * X)).mono_left inf_le_left).congr fun x => ?_
    simp [slope_def_field, inverseGaussian_zero, div_eq_mul_inv, mul_right_comm]
  · have hd := ((p.hasDerivAt x⁻¹).mul
      ((((hasDerivAt_id (x⁻¹)).pow 2).const_mul (-a)).exp)).comp x (hasDerivAt_inv hx.ne')
    convert hd.congr_of_eventuallyEq ?_ using 1
    · simp only [inverseGaussianNext, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
        inverseGaussian, if_neg hx.not_le, id_eq, Nat.cast_ofNat, pow_one]
      ring
    · filter_upwards [lt_mem_nhds hx] with y hy
      simp [inverseGaussian, hy.not_le]

theorem inverseGaussian_polynomial_differentiable {a : ℝ} (ha : 0 < a) (p : ℝ[X]) :
    Differentiable ℝ (fun x => p.eval x⁻¹ * inverseGaussian a x) :=
  fun x => (inverseGaussian_polynomial_hasDerivAt ha p x).differentiableAt

theorem inverseGaussian_polynomial_contDiff {a : ℝ} (ha : 0 < a) {n : ℕ∞} (p : ℝ[X]) :
    ContDiff ℝ n (fun x => p.eval x⁻¹ * inverseGaussian a x) := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) n
  induction m generalizing p with
  | zero => exact contDiff_zero.2 (inverseGaussian_polynomial_differentiable ha p).continuous
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.2 ⟨inverseGaussian_polynomial_differentiable ha p, by simp, ?_⟩
    convert ih (inverseGaussianNext a p) using 2
    exact (inverseGaussian_polynomial_hasDerivAt ha p _).deriv

theorem inverseGaussian_contDiff {a : ℝ} (ha : 0 < a) {n : ℕ∞} :
    ContDiff ℝ n (inverseGaussian a) := by
  simpa using inverseGaussian_polynomial_contDiff ha (1 : ℝ[X])

end FreshGradientMinimax
