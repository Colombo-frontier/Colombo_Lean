import Bilevel.RadialSecond
import Mathlib.Tactic.Module

/-! The actual second derivative of compression, in bounded compressed coordinates. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def triple (b v : E) : E →L[ℝ] E :=
  (innerSL ℝ b).smulRight v + ⟪b, v⟫ • ContinuousLinearMap.id ℝ E +
    (innerSL ℝ v).smulRight b

def cubic (b v : E) : E →L[ℝ] E := ⟪b, v⟫ • (innerSL ℝ b).smulRight b

def hessianSlice (R : ℝ) (u v : E) : E →L[ℝ] E :=
  (-(scale R u ^ 2) / R ^ 2) • triple (compress R u) v +
    (3 * scale R u ^ 2 / R ^ 4) • cubic (compress R u) v

theorem triple_apply (b v w : E) :
    triple b v w = ⟪b, w⟫ • v + ⟪b, v⟫ • w + ⟪v, w⟫ • b := by
  rfl

theorem cubic_apply (b v w : E) : cubic b v w = (⟪b, v⟫ * ⟪b, w⟫) • b := by
  simp [cubic, smul_smul]

theorem hessianSlice_hasFDerivAt (R : ℝ) (u v : E) :
    HasFDerivAt (fun z => compressDerivative R z v) (hessianSlice R u v) u := by
  have hs := scale_hasFDerivAt R u
  have hi : HasFDerivAt (fun z : E => ⟪z, v⟫) (innerSL ℝ v) u := by
    simpa only [real_inner_comm] using (innerSL ℝ v).hasFDerivAt (x := u)
  have hc := (((hasDerivAt_pow 3 (scale R u)).comp_hasFDerivAt u hs).mul hi).const_mul (R ^ 2)⁻¹
  have hd := (hs.smul_const v).sub (hc.smul (hasFDerivAt_id u))
  convert hd using 1
  · funext z
    rw [compressDerivative_apply]
    congr 1
    congr 1
    dsimp only [Function.comp_apply]
    ring
  · ext w
    simp only [hessianSlice, triple, cubic, scaleDerivative, compress,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, innerSL_apply, real_inner_smul_left,
      smul_eq_mul, ContinuousLinearMap.comp_apply, smul_smul, Function.comp_apply, id_eq]
    simp only [real_inner_comm v u, real_inner_comm v w]
    module

theorem triple_norm_bound (b v : E) : ‖triple b v‖ ≤ 3 * ‖b‖ * ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [triple_apply]
  have ht := (norm_add_le (⟪b, w⟫ • v + ⟪b, v⟫ • w) (⟪v, w⟫ • b)).trans
    (add_le_add_right (norm_add_le _ _) _)
  simp only [norm_smul, Real.norm_eq_abs] at ht
  have h0 := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm b w) (norm_nonneg v)
  have h1 := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm b v) (norm_nonneg w)
  have h2 := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm v w) (norm_nonneg b)
  nlinarith

theorem cubic_norm_bound (b v : E) : ‖cubic b v‖ ≤ ‖b‖ ^ 3 * ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [cubic_apply, norm_smul, Real.norm_eq_abs, abs_mul]
  have h0 := mul_le_mul (abs_real_inner_le_norm b v) (abs_real_inner_le_norm b w)
    (abs_nonneg _) (by positivity)
  have h := mul_le_mul_of_nonneg_right h0 (norm_nonneg b)
  nlinarith

theorem triple_sub (b c v : E) : triple b v - triple c v = triple (b - c) v := by
  ext w
  simp only [ContinuousLinearMap.sub_apply, triple_apply, inner_sub_left, sub_smul, smul_sub]
  abel

theorem triple_difference_bound (b c v : E) : ‖triple b v - triple c v‖ ≤ 3 * ‖b - c‖ * ‖v‖ := by
  rw [triple_sub]
  exact triple_norm_bound _ _

theorem cubic_difference_bound (R : ℝ) (hR : 0 ≤ R) (b c v : E)
    (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) :
    ‖cubic b v - cubic c v‖ ≤ 3 * R ^ 2 * ‖b - c‖ * ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have he : (cubic b v - cubic c v) w =
      (⟪b, v⟫ - ⟪c, v⟫) • rankOne b w +
        ⟪c, v⟫ • (rankOne b w - rankOne c w) := by
    simp only [ContinuousLinearMap.sub_apply, cubic_apply, rankOne, sub_smul, smul_sub, smul_smul]
    module
  have hi : |⟪b, v⟫ - ⟪c, v⟫| ≤ ‖b - c‖ * ‖v‖ := by
    rw [← inner_sub_left]
    exact abs_real_inner_le_norm _ _
  have hcv : |⟪c, v⟫| ≤ R * ‖v‖ :=
    (abs_real_inner_le_norm c v).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg v))
  have hrb : ‖rankOne b w‖ ≤ R ^ 2 * ‖w‖ := (rankOne_norm_bound b w).trans
    (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg b) hR).mpr hb) (norm_nonneg w))
  have hd := rankOne_difference_bound R b c w hb hc
  rw [he]
  calc
    _ ≤ ‖(⟪b, v⟫ - ⟪c, v⟫) • rankOne b w‖ +
        ‖⟪c, v⟫ • (rankOne b w - rankOne c w)‖ := norm_add_le _ _
    _ = |⟪b, v⟫ - ⟪c, v⟫| * ‖rankOne b w‖ +
        |⟪c, v⟫| * ‖rankOne b w - rankOne c w‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (‖b - c‖ * ‖v‖) * (R ^ 2 * ‖w‖) +
        (R * ‖v‖) * (2 * R * ‖b - c‖ * ‖w‖) :=
      add_le_add (mul_le_mul hi hrb (norm_nonneg _) (by positivity))
        (mul_le_mul hcv hd (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem actual_hessian_apply (R : ℝ) (u v w : E) :
    fderiv ℝ (compressDerivative R) u w v = hessianSlice R u v w := by
  have hd := ((compressDerivative_contDiff R 1).differentiable (by norm_num) u).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const v u)
  have hu := (hessianSlice_hasFDerivAt R u v).unique he
  have hh := congrArg (fun A : E →L[ℝ] E => A w) hu
  simpa using hh.symm

end Bilevel.RadialWrapper
