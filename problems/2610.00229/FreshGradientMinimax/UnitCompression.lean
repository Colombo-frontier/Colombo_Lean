import FreshGradientMinimax.QuadraticConvexity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The unit radial compression used by C.3, with its actual derivative.
Working first at unit radius keeps all analytic constants explicit. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def compressionFactor (x : E) : ℝ := (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹

def unitCompression (x : E) : E := compressionFactor x • x

def unitCompressionDerivative (x : E) : E →L[ℝ] E :=
  compressionFactor x • ContinuousLinearMap.id ℝ E -
    compressionFactor x ^ 3 • (innerSL ℝ x).smulRight x

omit [InnerProductSpace ℝ E] in
theorem compressionFactor_pos (x : E) : 0 < compressionFactor x := by
  unfold compressionFactor
  positivity

omit [InnerProductSpace ℝ E] in
theorem compressionFactor_le_one (x : E) : compressionFactor x ≤ 1 := by
  unfold compressionFactor
  apply (inv_le_one₀ (Real.sqrt_pos.mpr (by positivity))).mpr
  exact Real.one_le_sqrt.mpr (by nlinarith only [sq_nonneg ‖x‖])

omit [InnerProductSpace ℝ E] in
theorem compressionFactor_identity (x : E) : compressionFactor x ^ 2 * (1 + ‖x‖ ^ 2) = 1 := by
  unfold compressionFactor
  rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 + ‖x‖ ^ 2)]
  exact inv_mul_cancel₀ (by positivity : (1 + ‖x‖ ^ 2 : ℝ) ≠ 0)

theorem compressionFactor_contDiff {m : ℕ∞} : ContDiff ℝ m (compressionFactor : E → ℝ) := by
  have hp (x : E) : 0 < (1 : ℝ) + ‖x‖ ^ 2 := by positivity
  exact ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun x => (hp x).ne')).inv
    (fun x => (Real.sqrt_pos.mpr (hp x)).ne')

theorem compressionFactor_hasFDerivAt (x : E) :
    HasFDerivAt compressionFactor (-compressionFactor x ^ 3 • innerSL ℝ x) x := by
  have hp : 0 < (1 : ℝ) + ‖x‖ ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr hp
  have h := (hasDerivAt_inv hs.ne').comp_hasFDerivAt x
    (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1).sqrt hp.ne')
  apply h.congr_fderiv
  ext v
  simp only [compressionFactor, ContinuousLinearMap.smul_apply, innerSL_apply, smul_eq_mul]
  generalize Real.sqrt (1 + ‖x‖ ^ 2) = d at hs ⊢
  field_simp
  ring

theorem unitCompression_contDiff {m : ℕ∞} : ContDiff ℝ m (unitCompression : E → E) :=
  compressionFactor_contDiff.smul contDiff_id

theorem unitCompression_hasFDerivAt (x : E) :
    HasFDerivAt unitCompression (unitCompressionDerivative x) x := by
  apply ((compressionFactor_hasFDerivAt x).smul (hasFDerivAt_id x)).congr_fderiv
  ext v
  simp only [unitCompressionDerivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply, smul_eq_mul, neg_smul, smul_smul, ContinuousLinearMap.neg_apply, id_eq]
  module

theorem unitCompressionDerivative_apply (x v : E) :
    unitCompressionDerivative x v = compressionFactor x • v -
      (compressionFactor x ^ 3 * ⟪x, v⟫_ℝ) • x := by
  simp only [unitCompressionDerivative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply, smul_smul]

theorem unitCompressionDerivative_selfAdjoint (x v w : E) :
    ⟪unitCompressionDerivative x v, w⟫_ℝ = ⟪v, unitCompressionDerivative x w⟫_ℝ := by
  simp only [unitCompressionDerivative_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    inner_smul_right, real_inner_comm v x]
  ring

theorem unitCompression_norm_le_one (x : E) : ‖unitCompression x‖ ≤ 1 := by
  rw [unitCompression, norm_smul, Real.norm_eq_abs, abs_of_pos (compressionFactor_pos x)]
  have h := compressionFactor_identity x
  have hn := compressionFactor_pos x
  nlinarith only [h, sq_nonneg (compressionFactor x), norm_nonneg x,
    mul_nonneg hn.le (norm_nonneg x)]

theorem unitCompression_norm_le (x : E) : ‖unitCompression x‖ ≤ ‖x‖ := by
  rw [unitCompression, norm_smul, Real.norm_eq_abs, abs_of_pos (compressionFactor_pos x)]
  exact mul_le_of_le_one_left (norm_nonneg x) (compressionFactor_le_one x)

theorem rankOne_contraction {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (x v : E)
    (hcx : c * ‖x‖ ^ 2 ≤ 2 * a) : ‖a • v - (c * ⟪x, v⟫_ℝ) • x‖ ≤ a * ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg v))).mp
  have h := mul_nonneg (mul_nonneg hc (sq_nonneg ⟪v, x⟫_ℝ)) (sub_nonneg.mpr hcx)
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, inner_smul_right, real_inner_comm v x]
  nlinarith only [h]

theorem unitCompressionDerivative_norm_apply (x v : E) :
    ‖unitCompressionDerivative x v‖ ≤ compressionFactor x * ‖v‖ := by
  rw [unitCompressionDerivative_apply]
  apply rankOne_contraction (compressionFactor_pos x).le (pow_nonneg (compressionFactor_pos x).le 3)
  have h := congrArg (fun q : ℝ => compressionFactor x * q) (compressionFactor_identity x)
  dsimp only at h
  nlinarith only [h, pow_nonneg (compressionFactor_pos x).le 3, (compressionFactor_pos x).le]

theorem unitCompressionDerivative_norm (x : E) : ‖unitCompressionDerivative x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  exact (unitCompressionDerivative_norm_apply x v).trans
    (mul_le_mul_of_nonneg_right (compressionFactor_le_one x) (norm_nonneg v))

theorem unitCompression_zero : unitCompression (0 : E) = 0 := by simp [unitCompression]

end FreshGradientMinimax
