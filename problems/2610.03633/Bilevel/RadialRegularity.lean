import Bilevel.RadialCompression

/-! Global smoothness and derivative estimates for radial compression. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scale_contDiff (R : ℝ) (k : ℕ) : ContDiff ℝ k (scale (E := E) R) := by
  have hq : ContDiff ℝ k (fun u : E => 1 + ‖u‖ ^ 2 / R ^ 2) :=
    contDiff_const.add ((contDiff_norm_sq ℝ).div_const _)
  exact (hq.sqrt (fun u => (radicand_pos R u).ne')).inv (fun u => (root_pos R u).ne')

theorem compress_contDiff (R : ℝ) (k : ℕ) : ContDiff ℝ k (compress (E := E) R) :=
  (scale_contDiff R k).smul contDiff_id

theorem compressed_radius_bound (R : ℝ) (hR : 0 < R) (u : E) : scale R u * ‖u‖ ≤ R := by
  simpa only [compress, norm_smul, Real.norm_eq_abs, abs_of_pos (scale_pos R u)] using
    compress_norm_le_radius R hR u

theorem scale_factor_bound (R : ℝ) (hR : 0 < R) (u : E) :
    scale R u ^ 3 / R ^ 2 * ‖u‖ ≤ 1 / R := by
  have ha := scale_pos R u
  have ha1 := scale_le_one R u
  have ha2 : scale R u ^ 2 ≤ 1 := by nlinarith
  have hb := compressed_radius_bound R hR u
  have hm := mul_le_mul_of_nonneg_right ha2 (mul_nonneg ha.le (norm_nonneg u))
  have hc : scale R u ^ 3 * ‖u‖ ≤ R := by nlinarith
  calc
    _ = (scale R u ^ 3 * ‖u‖) / R ^ 2 := by ring
    _ ≤ R / R ^ 2 := div_le_div_of_nonneg_right hc (sq_nonneg R)
    _ = 1 / R := by field_simp; ring

theorem scaleDerivative_norm_le (R : ℝ) (hR : 0 < R) (u : E) : ‖scaleDerivative R u‖ ≤ 1 / R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have ha := scale_pos R u
  have hcoef : 0 ≤ scale R u ^ 3 / R ^ 2 := by positivity
  have he : ‖scaleDerivative R u v‖ = (scale R u ^ 3 / R ^ 2) * |⟪u, v⟫| := by
    simp only [scaleDerivative, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_div, abs_neg,
      abs_of_nonneg (pow_nonneg ha.le 3), abs_of_nonneg (sq_nonneg R)]
    rfl
  rw [he]
  calc
    _ ≤ (scale R u ^ 3 / R ^ 2) * (‖u‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm u v) hcoef
    _ = (scale R u ^ 3 / R ^ 2 * ‖u‖) * ‖v‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (scale_factor_bound R hR u) (norm_nonneg v)

theorem scale_lipschitz (R : ℝ) (hR : 0 < R) :
    LipschitzWith ⟨1 / R, by positivity⟩ (scale (E := E) R) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun u => (scale_hasFDerivAt R u).differentiableAt)
  intro u
  rw [(scale_hasFDerivAt R u).fderiv]
  exact_mod_cast scaleDerivative_norm_le R hR u

end Bilevel.RadialWrapper
