import Bilevel.RadialThird

/-! Pointwise decay estimates needed by the global public radial extension.
Unlike a uniform bound, the scale factor cancels arbitrarily large normal
coordinates in the extension's second and third derivatives. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem compressDerivative_norm_le_scale (R : ℝ) (hR : 0 < R) (u v : E) :
    ‖compressDerivative R u v‖ ≤ scale R u*‖v‖ := by
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
  change ‖compressDerivative R u v‖≤a*‖v‖
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha.le (norm_nonneg _))).mp
    (by simpa only [mul_pow] using hn)

theorem compressDerivative_opNorm_le_scale (R : ℝ) (hR : 0<R) (z : E) :
    ‖compressDerivative R z‖≤scale R z := by
  apply ContinuousLinearMap.opNorm_le_bound _ (scale_pos R z).le
  exact compressDerivative_norm_le_scale R hR z

theorem hessianSlice_norm_le_scale (R : ℝ) (hR : 0<R) (z v : E) :
    ‖hessianSlice R z v‖≤(6*scale R z^2/R)*‖v‖ := by
  rw [hessianSlice_shape,norm_smul (scale R z^2) (hessianShape R (compress R z) v),
    Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  convert mul_le_mul_of_nonneg_left
    (hessianShape_bound R hR (compress R z) v (compress_norm_le_radius R hR z))
    (sq_nonneg (scale R z)) using 1
  ring

end Bilevel.RadialWrapper
