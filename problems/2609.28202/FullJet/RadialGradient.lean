import FullJet.Radial
import FullJet.RadialBarrierAlgebra
import Mathlib.Analysis.Calculus.Gradient.Basic

open scoped InnerProductSpace

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def alignmentGradient (θ x : E) : E :=
  (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ • θ -
    (⟪θ, x⟫_ℝ / Real.sqrt (1 + ‖x‖ ^ 2) ^ 3) • x

theorem alignment_hasFDerivAt (θ x : E) :
    HasFDerivAt (alignment θ) (innerSL ℝ (alignmentGradient θ x)) x := by
  have hpos : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr hpos
  have hr := (hasDerivAt_inv hs.ne').comp_hasFDerivAt x
    (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1).sqrt hpos.ne')
  have h := (innerSL ℝ θ).hasFDerivAt.mul hr
  convert h using 1
  · funext y
    simp [alignment, radial, real_inner_smul_right, mul_comm]
  · ext v
    simp only [alignmentGradient, innerSL_apply, inner_sub_left,
      real_inner_smul_left, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Function.comp_apply]
    generalize hd : Real.sqrt (1 + ‖x‖ ^ 2) = d at hs ⊢
    field_simp
    <;> ring

theorem alignment_hasGradientAt [CompleteSpace E] (θ x : E) :
    HasGradientAt (alignment θ) (alignmentGradient θ x) x :=
  alignment_hasFDerivAt θ x

theorem alignment_gradient [CompleteSpace E] (θ x : E) :
    gradient (alignment θ) x = alignmentGradient θ x :=
  (alignment_hasGradientAt θ x).gradient

theorem radial_alignment_coordinates (θ x : E) (hθ : ‖θ‖ = 1) :
    (1 + ‖x‖ ^ 2)⁻¹ + alignment θ x ^ 2 ≤ 1 := by
  let d := Real.sqrt (1 + ‖x‖ ^ 2)
  have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d ^ 2 = 1 + ‖x‖ ^ 2 := Real.sq_sqrt (by positivity)
  have ha : |⟪θ, x⟫_ℝ| ≤ ‖x‖ := by simpa only [hθ, one_mul] using abs_real_inner_le_norm θ x
  have ht2 : ⟪θ, x⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_abs ⟪θ, x⟫_ℝ, abs_nonneg ⟪θ, x⟫_ℝ, norm_nonneg x]
  have hq : alignment θ x = ⟪θ, x⟫_ℝ / d := by
    simp [alignment, radial, d, real_inner_smul_right, div_eq_mul_inv, mul_comm]
  rw [hq, ← hd2, div_pow, inv_eq_one_div, ← add_div]
  exact (div_le_one (pow_pos hd 2)).mpr (by nlinarith)

theorem alignmentGradient_inner (θ x : E) :
    ⟪x, alignmentGradient θ x⟫_ℝ = alignment θ x * (1 + ‖x‖ ^ 2)⁻¹ := by
  let d := Real.sqrt (1 + ‖x‖ ^ 2)
  have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d ^ 2 = 1 + ‖x‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hnorm : ‖x‖ ^ 2 = d ^ 2 - 1 := by linarith
  simp only [alignmentGradient, alignment, radial, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm x θ]
  change d⁻¹ * ⟪x, θ⟫_ℝ - (⟪x, θ⟫_ℝ / d ^ 3) * ‖x‖ ^ 2 =
    (d⁻¹ * ⟪x, θ⟫_ℝ) * (1 + ‖x‖ ^ 2)⁻¹
  rw [← hd2, hnorm]
  field_simp
  <;> ring

theorem alignmentGradient_norm_sq (θ x : E) (hθ : ‖θ‖ = 1) :
    ‖alignmentGradient θ x‖ ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ *
      (1 - alignment θ x ^ 2 - alignment θ x ^ 2 * (1 + ‖x‖ ^ 2)⁻¹) := by
  let d := Real.sqrt (1 + ‖x‖ ^ 2)
  have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d ^ 2 = 1 + ‖x‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hnorm : ‖x‖ ^ 2 = d ^ 2 - 1 := by linarith
  simp only [alignmentGradient, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, hθ, one_pow, mul_one, real_inner_smul_left, real_inner_smul_right,
    alignment, radial]
  change (d⁻¹) ^ 2 - 2 * ((⟪θ, x⟫_ℝ / d ^ 3) * (d⁻¹ * ⟪θ, x⟫_ℝ)) +
    (⟪θ, x⟫_ℝ / d ^ 3) ^ 2 * ‖x‖ ^ 2 =
    (1 + ‖x‖ ^ 2)⁻¹ * (1 - (d⁻¹) ^ 2 * ⟪θ, x⟫_ℝ ^ 2 -
      (d⁻¹) ^ 2 * ⟪θ, x⟫_ℝ ^ 2 * (1 + ‖x‖ ^ 2)⁻¹)
  rw [← hd2, hnorm]
  field_simp
  <;> ring

theorem radial_gradient_block_norm_sq (θ x : E) (hθ : ‖θ‖ = 1) (c : ℝ) :
    ‖(33 / 16 : ℝ) • x - c • alignmentGradient θ x‖ ^ 2 =
      radialGradientSq (alignment θ x) (1 + ‖x‖ ^ 2)⁻¹ c := by
  rw [norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
    real_inner_smul_right, alignmentGradient_inner, alignmentGradient_norm_sq θ x hθ]
  simp only [radialGradientSq, inv_inv]
  ring

/-- The single-block radial gradient barrier with an explicit universal constant. -/
theorem radial_gradient_block_lower_bound (θ x : E) (hθ : ‖θ‖ = 1) (c : ℝ)
    (hc : 1 ≤ c) (hq : alignment θ x ≤ 9 / 32) :
    (1 / 4 : ℝ) ≤ ‖(33 / 16 : ℝ) • x - c • alignmentGradient θ x‖ := by
  have h := radialGradientSq_lower_bound (alignment θ x) (1 + ‖x‖ ^ 2)⁻¹ c
    (by positivity) (radial_alignment_coordinates θ x hθ) hq hc
  rw [← radial_gradient_block_norm_sq θ x hθ c] at h
  nlinarith [norm_nonneg ((33 / 16 : ℝ) • x - c • alignmentGradient θ x)]

end FullJet
