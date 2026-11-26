import FreshGradientMinimax.UnitCompression
import Mathlib.Analysis.Normed.Module.Convex

/-! The explicit second derivative of radial compression and its sharp-enough
dimension-free bound 3. No Hessian or smoothness bound is assumed. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def unitCompressionSecond (x v : E) : E →L[ℝ] E :=
  -compressionFactor x ^ 3 • ((innerSL ℝ x).smulRight v +
    ⟪x, v⟫_ℝ • ContinuousLinearMap.id ℝ E + (innerSL ℝ v).smulRight x) +
    (3 * compressionFactor x ^ 5 * ⟪x, v⟫_ℝ) • (innerSL ℝ x).smulRight x

theorem compressionCube_hasFDerivAt (x : E) :
    HasFDerivAt (fun z : E => compressionFactor z ^ 3)
      ((-3 * compressionFactor x ^ 5) • innerSL ℝ x) x := by
  apply ((hasDerivAt_pow 3 (compressionFactor x)).comp_hasFDerivAt x
    (compressionFactor_hasFDerivAt x)).congr_fderiv
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  norm_num
  ring

theorem unitCompressionSecond_apply (x v h : E) :
    unitCompressionSecond x v h =
      -compressionFactor x ^ 3 • (⟪x, h⟫_ℝ • v + ⟪x, v⟫_ℝ • h + ⟪v, h⟫_ℝ • x) +
        (3 * compressionFactor x ^ 5 * ⟪x, v⟫_ℝ * ⟪x, h⟫_ℝ) • x := by
  simp only [unitCompressionSecond, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply, smul_smul]

theorem unitCompressionDerivative_hasFDerivAt_apply (x v : E) :
    HasFDerivAt (fun z : E => unitCompressionDerivative z v) (unitCompressionSecond x v) x := by
  have hd := ((compressionFactor_hasFDerivAt x).smul_const v).sub
    (((compressionCube_hasFDerivAt x).mul (innerSL ℝ v).hasFDerivAt).smul (hasFDerivAt_id x))
  convert hd using 1
  · funext z
    simp only [unitCompressionDerivative_apply, innerSL_apply, real_inner_comm v z, id_eq]
  · ext h
    simp only [unitCompressionSecond_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply, smul_eq_mul, real_inner_comm v x, smul_smul, ContinuousLinearMap.neg_apply, id_eq]
    module

omit [InnerProductSpace ℝ E] in
theorem compression_second_coefficient (x : E) :
    compressionFactor x ^ 3 * ‖x‖ + compressionFactor x ^ 5 * ‖x‖ ^ 3 ≤ 1 := by
  let a := compressionFactor x
  let b := a * ‖x‖
  have ha : 0 ≤ a := (compressionFactor_pos x).le
  have hb : 0 ≤ b := mul_nonneg ha (norm_nonneg x)
  have hid : a ^ 2 + b ^ 2 = 1 := by
    have h := compressionFactor_identity x
    dsimp only [a, b]
    nlinarith only [h]
  have hb1 : b ≤ 1 := by nlinarith only [hid, sq_nonneg a, hb]
  have he : a ^ 2 * b + a ^ 2 * b ^ 3 = b - b ^ 5 := by
    have ha2 : a ^ 2 = 1 - b ^ 2 := by linarith only [hid]
    rw [ha2]
    ring
  have hc : a ^ 2 * b + a ^ 2 * b ^ 3 ≤ 1 := by
    rw [he]
    linarith only [hb1, pow_nonneg hb 5]
  dsimp only [a, b] at hc
  nlinarith only [hc]

theorem unitCompressionSecond_norm_apply (x v h : E) :
    ‖unitCompressionSecond x v h‖ ≤ 3 * ‖v‖ * ‖h‖ := by
  have ha := (compressionFactor_pos x).le
  have hxh := abs_real_inner_le_norm x h
  have hxv := abs_real_inner_le_norm x v
  have hvh := abs_real_inner_le_norm v h
  have hs : ‖⟪x, h⟫_ℝ • v + ⟪x, v⟫_ℝ • h + ⟪v, h⟫_ℝ • x‖ ≤ 3 * ‖x‖ * ‖v‖ * ‖h‖ := by
    have h1 := norm_add_le (⟪x, h⟫_ℝ • v + ⟪x, v⟫_ℝ • h) (⟪v, h⟫_ℝ • x)
    have h2 := norm_add_le (⟪x, h⟫_ℝ • v) (⟪x, v⟫_ℝ • h)
    simp only [norm_smul, Real.norm_eq_abs] at h1 h2
    have h3 := mul_le_mul_of_nonneg_right hxh (norm_nonneg v)
    have h4 := mul_le_mul_of_nonneg_right hxv (norm_nonneg h)
    have h5 := mul_le_mul_of_nonneg_right hvh (norm_nonneg x)
    nlinarith only [h1, h2, h3, h4, h5]
  have ht : |⟪x, v⟫_ℝ| * |⟪x, h⟫_ℝ| * ‖x‖ ≤ ‖x‖ ^ 3 * ‖v‖ * ‖h‖ := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul hxv hxh (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg v))) (norm_nonneg x)
    nlinarith only [hh]
  have h1 := mul_le_mul_of_nonneg_left hs (pow_nonneg ha 3)
  have h2 := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 3 * compressionFactor x ^ 5)
  have h3 := mul_le_mul_of_nonneg_right (compression_second_coefficient x)
    (by positivity : 0 ≤ 3 * ‖v‖ * ‖h‖)
  rw [unitCompressionSecond_apply]
  have hsum := norm_add_le
    (-compressionFactor x ^ 3 • (⟪x, h⟫_ℝ • v + ⟪x, v⟫_ℝ • h + ⟪v, h⟫_ℝ • x))
    ((3 * compressionFactor x ^ 5 * ⟪x, v⟫_ℝ * ⟪x, h⟫_ℝ) • x)
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, abs_pow,
    abs_of_nonneg ha, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at hsum
  nlinarith only [hsum, h1, h2, h3]

theorem unitCompressionSecond_norm (x v : E) : ‖unitCompressionSecond x v‖ ≤ 3 * ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact unitCompressionSecond_norm_apply x v

theorem unitCompressionDerivative_sub_norm (x y : E) :
    ‖unitCompressionDerivative x - unitCompressionDerivative y‖ ≤ 3 * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have h := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (unitCompressionDerivative_hasFDerivAt_apply z v).hasFDerivWithinAt)
    (fun z _ => unitCompressionSecond_norm z v) (Set.mem_univ y) (Set.mem_univ x)
  change ‖unitCompressionDerivative x v - unitCompressionDerivative y v‖ ≤ _
  nlinarith only [h]

theorem unitCompression_sub_norm (x y : E) : ‖unitCompression x - unitCompression y‖ ≤ ‖x - y‖ := by
  have h := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (unitCompression_hasFDerivAt z).hasFDerivWithinAt)
    (fun z _ => unitCompressionDerivative_norm z) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [one_mul] using h

end FreshGradientMinimax
