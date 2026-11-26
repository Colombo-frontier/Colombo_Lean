import Bilevel.RadialWrapper
import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative bounds for the actual radial compression. -/

noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem scale_radius_identity (R : ℝ) (hR : 0 < R) (u : E) :
    scale R u ^ 2 * (R ^ 2 + ‖u‖ ^ 2) = R ^ 2 := by
  have h := congrArg (fun z : ℝ => z * R ^ 2) (scale_square R u)
  field_simp [hR.ne'] at h
  nlinarith

omit [InnerProductSpace ℝ E] in
theorem scale_inverse_root (R : ℝ) (u : E) :
    scale R u * Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2) = 1 :=
  inv_mul_cancel₀ (root_pos R u).ne'

omit [InnerProductSpace ℝ E] in
theorem scale_interior_lower (R : ℝ) (hR : 0 < R) (u : E) (hu : ‖u‖ ≤ R) :
    2 / 3 ≤ scale R u := by
  have hn : ‖u‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg u) hR.le).mpr hu
  have hq : ‖u‖ ^ 2 / R ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hR)).mpr hn
  have hroot := root_square R u
  have hs := root_pos R u
  have hb : Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2) ≤ 3 / 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hb (scale_pos R u).le
  rw [scale_inverse_root] at hm
  linarith

omit [InnerProductSpace ℝ E] in
theorem compressed_radius_exterior_lower (R : ℝ) (hR : 0 < R) (u : E) (hu : R ≤ ‖u‖) :
    2 * R / 3 ≤ scale R u * ‖u‖ := by
  have hn : R ^ 2 ≤ ‖u‖ ^ 2 := (sq_le_sq₀ hR.le (norm_nonneg u)).mpr hu
  have hid : (Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2) * R) ^ 2 = R ^ 2 + ‖u‖ ^ 2 := by
    rw [mul_pow, root_square]
    field_simp
  have hp : 0 < Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2) * R := mul_pos (root_pos R u) hR
  have hb : Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2) * R ≤ 3 / 2 * ‖u‖ := by nlinarith [norm_nonneg u]
  have hm := mul_le_mul_of_nonneg_left hb (scale_pos R u).le
  rw [← mul_assoc, scale_inverse_root, one_mul] at hm
  linarith

theorem compressDerivative_norm_le (R : ℝ) (hR : 0 < R) (u v : E) :
    ‖compressDerivative R u v‖ ≤ ‖v‖ := by
  let a := scale R u
  let c := a ^ 3 / R ^ 2
  have ha : 0 < a := scale_pos R u
  have ha1 : a ≤ 1 := scale_le_one R u
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hid := scale_radius_identity R hR u
  have hcn : c * ‖u‖ ^ 2 ≤ a := by
    have han : a ^ 2 * ‖u‖ ^ 2 ≤ R ^ 2 := by
      change a ^ 2 * (R ^ 2 + ‖u‖ ^ 2) = R ^ 2 at hid
      nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg R)]
    have hm := mul_le_mul_of_nonneg_left han ha.le
    dsimp [c]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith
  have hcn2 : c ^ 2 * ‖u‖ ^ 2 ≤ a * c := by
    nlinarith [mul_le_mul_of_nonneg_right hcn hc]
  have hterm := mul_le_mul_of_nonneg_right hcn2 (sq_nonneg ⟪u, v⟫)
  have hn : ‖compressDerivative R u v‖ ^ 2 ≤ a ^ 2 * ‖v‖ ^ 2 := by
    rw [compressDerivative_apply, norm_sub_sq_real]
    change ‖a • v‖ ^ 2 - 2 * ⟪a • v, (c * ⟪u, v⟫) • u⟫ +
      ‖(c * ⟪u, v⟫) • u‖ ^ 2 ≤ a ^ 2 * ‖v‖ ^ 2
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right]
    have hi : ⟪v, u⟫ = ⟪u, v⟫ := real_inner_comm _ _
    rw [hi]
    nlinarith [mul_nonneg (mul_nonneg ha.le hc) (sq_nonneg ⟪u, v⟫)]
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hv := mul_le_mul_of_nonneg_right ha2 (sq_nonneg ‖v‖)
  nlinarith [norm_nonneg (compressDerivative R u v), norm_nonneg v]

theorem compressDerivative_opNorm_le (R : ℝ) (hR : 0 < R) (u : E) :
    ‖compressDerivative R u‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa using compressDerivative_norm_le R hR u v

theorem compress_lipschitz (R : ℝ) (hR : 0 < R) : LipschitzWith 1 (compress (E := E) R) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun u => (compress_hasFDerivAt R u).differentiableAt)
  intro u
  rw [(compress_hasFDerivAt R u).fderiv]
  exact_mod_cast compressDerivative_opNorm_le R hR u

end Bilevel.RadialWrapper
