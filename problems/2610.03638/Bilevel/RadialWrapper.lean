import Bilevel.WrapperBudget
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Actual radial compression and coercive wrapper derivatives -/

noncomputable section
open scoped RealInnerProductSpace

namespace Bilevel.RadialWrapper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def scale (R : ℝ) (u : E) : ℝ := (Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2))⁻¹
def compress (R : ℝ) (u : E) : E := scale R u • u
def bowl (ν R : ℝ) (u : E) : ℝ := ν * R ^ 2 * (Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2) - 1)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem radicand_pos (R : ℝ) (u : E) : 0 < 1 + ‖u‖ ^ 2 / R ^ 2 := by positivity
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem root_pos (R : ℝ) (u : E) : 0 < Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2) :=
  Real.sqrt_pos.mpr (radicand_pos R u)
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem scale_pos (R : ℝ) (u : E) : 0 < scale R u := inv_pos.mpr (root_pos R u)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem scale_le_one (R : ℝ) (u : E) : scale R u ≤ 1 := by
  unfold scale
  apply inv_le_one_of_one_le₀
  apply Real.one_le_sqrt.mpr
  have h : 0 ≤ ‖u‖ ^ 2 / R ^ 2 := by positivity
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem root_square (R : ℝ) (u : E) :
    Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2) ^ 2 = 1 + ‖u‖ ^ 2 / R ^ 2 :=
  Real.sq_sqrt (radicand_pos R u).le

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem scale_square (R : ℝ) (u : E) :
    scale R u ^ 2 * (1 + ‖u‖ ^ 2 / R ^ 2) = 1 := by
  rw [← root_square]
  unfold scale
  field_simp

omit [CompleteSpace E] in
theorem compress_norm_le_radius (R : ℝ) (hR : 0 < R) (u : E) : ‖compress R u‖ ≤ R := by
  have hs := scale_square R u
  have hrel : scale R u ^ 2 * (R ^ 2 + ‖u‖ ^ 2) = R ^ 2 := by
    have hm := congrArg (fun z : ℝ => z * R ^ 2) hs
    field_simp at hm
    nlinarith
  rw [compress, norm_smul, Real.norm_eq_abs, abs_of_pos (scale_pos R u)]
  nlinarith [sq_nonneg (scale R u), norm_nonneg u, scale_pos R u]

def scaleDerivative (R : ℝ) (u : E) : E →L[ℝ] ℝ :=
  (-(scale R u) ^ 3 / R ^ 2) • innerSL ℝ u

omit [CompleteSpace E] in
theorem radicand_hasFDerivAt (R : ℝ) (u : E) :
    HasFDerivAt (fun v : E => 1 + ‖v‖ ^ 2 / R ^ 2) ((2 / R ^ 2) • innerSL ℝ u) u := by
  have h := ((hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_mul ((R ^ 2)⁻¹)).const_add 1
  convert h using 1
  · funext v
    simp [div_eq_mul_inv, mul_comm]
  · ext v
    simp
    ring

omit [CompleteSpace E] in
theorem scale_hasFDerivAt (R : ℝ) (u : E) :
    HasFDerivAt (scale R) (scaleDerivative R u) u := by
  have hq := radicand_hasFDerivAt R u
  have hs := hq.sqrt (radicand_pos R u).ne'
  have h := (hasDerivAt_inv (root_pos R u).ne').comp_hasFDerivAt u hs
  convert h using 1
  ext v
  simp only [scaleDerivative, scale, ContinuousLinearMap.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

def compressDerivative (R : ℝ) (u : E) : E →L[ℝ] E :=
  scale R u • ContinuousLinearMap.id ℝ E + (scaleDerivative R u).smulRight u

omit [CompleteSpace E] in
theorem compress_hasFDerivAt (R : ℝ) (u : E) :
    HasFDerivAt (compress R) (compressDerivative R u) u := by
  have h := (scale_hasFDerivAt R u).smul (hasFDerivAt_id u)
  exact h

omit [CompleteSpace E] in
theorem compressDerivative_apply (R : ℝ) (u v : E) :
    compressDerivative R u v = scale R u • v -
      ((scale R u) ^ 3 / R ^ 2 * ⟪u, v⟫) • u := by
  simp [compressDerivative, scaleDerivative, sub_eq_add_neg, neg_div]

theorem bowl_hasGradientAt (ν R : ℝ) (hR : 0 < R) (u : E) :
    HasGradientAt (bowl ν R) ((ν * scale R u) • u) u := by
  have hq := radicand_hasFDerivAt R u
  have h := ((hq.sqrt (radicand_pos R u).ne').sub_const 1).const_mul (ν * R ^ 2)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h using 1
  ext v
  simp [InnerProductSpace.toDual_apply, scale, inner_smul_left]
  field_simp
  ring

def wrapped {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (ν R : ℝ) (H : Z → ℝ) (projection : E →L[ℝ] Z) (u : E) : ℝ :=
  H (projection (compress R u)) + bowl ν R u

def wrappedGradient (ν R : ℝ) (u h : E) : E :=
  scale R u • h + (ν * scale R u - (scale R u) ^ 3 / R ^ 2 * ⟪u, h⟫) • u

theorem wrapped_hasGradientAt {Z : Type*} [NormedAddCommGroup Z]
    [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (ν R : ℝ) (hR : 0 < R) (H : Z → ℝ) (projection : E →L[ℝ] Z) (u : E) (h : Z)
    (hH : HasGradientAt H h (projection (compress R u))) :
    HasGradientAt (wrapped ν R H projection) (wrappedGradient ν R u (projection.adjoint h)) u := by
  have hc := (projection.hasFDerivAt.comp u (compress_hasFDerivAt R u))
  have hd := (hH.hasFDerivAt.comp u hc).add (bowl_hasGradientAt ν R hR u).hasFDerivAt
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hd using 1
  ext v
  simp only [wrappedGradient, InnerProductSpace.toDual_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, real_inner_smul_left, compressDerivative_apply,
    map_sub, map_smul, inner_sub_right, real_inner_smul_right]
  simp only [← ContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.smul_apply,
    InnerProductSpace.toDual_apply, smul_eq_mul]
  have he : ⟪projection.adjoint h, u⟫ = ⟪projection u, h⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact real_inner_comm _ _
  rw [he]
  ring

end Bilevel.RadialWrapper
