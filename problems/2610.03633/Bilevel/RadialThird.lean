import Bilevel.RadialHessian

/-! A dimension-independent third derivative bound for radial compression. -/
noncomputable section
set_option synthInstance.maxSize 1024
open scoped RealInnerProductSpace
namespace Bilevel.RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def hessianShape (R : ℝ) (b v : E) : E →L[ℝ] E :=
  (-(1 / R ^ 2)) • triple b v + (3 / R ^ 4) • cubic b v

theorem hessianSlice_shape (R : ℝ) (u v : E) :
    hessianSlice R u v = (scale R u ^ 2) • hessianShape R (compress R u) v := by
  unfold hessianSlice hessianShape
  module

theorem hessianShape_bound (R : ℝ) (hR : 0 < R) (b v : E) (hb : ‖b‖ ≤ R) :
    ‖hessianShape R b v‖ ≤ (6 / R) * ‖v‖ := by
  have ht : ‖triple b v‖ ≤ 3 * R * ‖v‖ := (triple_norm_bound b v).trans (by nlinarith [norm_nonneg v])
  have hc : ‖cubic b v‖ ≤ R ^ 3 * ‖v‖ := (cubic_norm_bound b v).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg b) hb 3) (norm_nonneg v))
  calc
    _ ≤ ‖(-(1 / R ^ 2)) • triple b v‖ + ‖(3 / R ^ 4) • cubic b v‖ := norm_add_le _ _
    _ = (1 / R ^ 2) * ‖triple b v‖ + (3 / R ^ 4) * ‖cubic b v‖ := by
      rw [norm_smul (-(1 / R ^ 2)) (triple b v), norm_smul (3 / R ^ 4) (cubic b v)]
      simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 1 / R ^ 2),
        abs_of_nonneg (by positivity : 0 ≤ 3 / R ^ 4)]
    _ ≤ (1 / R ^ 2) * (3 * R * ‖v‖) + (3 / R ^ 4) * (R ^ 3 * ‖v‖) :=
      add_le_add (mul_le_mul_of_nonneg_left ht (by positivity))
        (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = _ := by field_simp; ring

theorem hessianShape_difference (R : ℝ) (hR : 0 < R) (b c v : E)
    (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) :
    ‖hessianShape R b v - hessianShape R c v‖ ≤ (12 / R ^ 2) * ‖b - c‖ * ‖v‖ := by
  have he : hessianShape R b v - hessianShape R c v =
      (-(1 / R ^ 2)) • (triple b v - triple c v) +
        (3 / R ^ 4) • (cubic b v - cubic c v) := by
    simp only [hessianShape, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖(-(1 / R ^ 2)) • (triple b v - triple c v)‖ +
        ‖(3 / R ^ 4) • (cubic b v - cubic c v)‖ := norm_add_le _ _
    _ = (1 / R ^ 2) * ‖triple b v - triple c v‖ +
        (3 / R ^ 4) * ‖cubic b v - cubic c v‖ := by
      rw [norm_smul (-(1 / R ^ 2)) (triple b v - triple c v),
        norm_smul (3 / R ^ 4) (cubic b v - cubic c v)]
      simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 1 / R ^ 2),
        abs_of_nonneg (by positivity : 0 ≤ 3 / R ^ 4)]
    _ ≤ (1 / R ^ 2) * (3 * ‖b - c‖ * ‖v‖) +
        (3 / R ^ 4) * (3 * R ^ 2 * ‖b - c‖ * ‖v‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (triple_difference_bound b c v) (by positivity))
        (mul_le_mul_of_nonneg_left (cubic_difference_bound R hR.le b c v hb hc) (by positivity))
    _ = _ := by field_simp; ring

theorem scale_square_difference (R : ℝ) (hR : 0 < R) (u w : E) :
    |scale R u ^ 2 - scale R w ^ 2| ≤ (2 / R) * ‖u - w‖ := by
  have hu := scale_pos R u
  have hw := scale_pos R w
  have hsum : |scale R u + scale R w| ≤ 2 := by
    rw [abs_of_pos (add_pos hu hw)]
    linarith [scale_le_one R u, scale_le_one R w]
  have hd := (scale_lipschitz R hR).norm_sub_le u w
  change |scale R u - scale R w| ≤ (1 / R) * ‖u - w‖ at hd
  rw [show scale R u ^ 2 - scale R w ^ 2 =
    (scale R u - scale R w) * (scale R u + scale R w) by ring, abs_mul]
  exact (mul_le_mul hd hsum (abs_nonneg _) (by positivity)).trans_eq (by ring)

theorem hessianSlice_difference (R : ℝ) (hR : 0 < R) (u w v : E) :
    ‖hessianSlice R u v - hessianSlice R w v‖ ≤ (24 / R ^ 2) * ‖u - w‖ * ‖v‖ := by
  have he : hessianSlice R u v - hessianSlice R w v =
      (scale R u ^ 2 - scale R w ^ 2) • hessianShape R (compress R u) v +
        (scale R w ^ 2) • (hessianShape R (compress R u) v - hessianShape R (compress R w) v) := by
    rw [hessianSlice_shape, hessianSlice_shape]
    module
  have hw : scale R w ^ 2 ≤ 1 := by nlinarith [scale_pos R w, scale_le_one R w]
  have hd : ‖hessianShape R (compress R u) v - hessianShape R (compress R w) v‖ ≤
      (12 / R ^ 2) * ‖u - w‖ * ‖v‖ :=
    (hessianShape_difference R hR _ _ v (compress_norm_le_radius R hR u) (compress_norm_le_radius R hR w)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by
        simpa using (compress_lipschitz R hR).norm_sub_le u w) (by positivity)) (norm_nonneg v))
  rw [he]
  calc
    _ ≤ ‖(scale R u ^ 2 - scale R w ^ 2) • hessianShape R (compress R u) v‖ +
        ‖(scale R w ^ 2) • (hessianShape R (compress R u) v - hessianShape R (compress R w) v)‖ := norm_add_le _ _
    _ = |scale R u ^ 2 - scale R w ^ 2| * ‖hessianShape R (compress R u) v‖ +
        scale R w ^ 2 * ‖hessianShape R (compress R u) v - hessianShape R (compress R w) v‖ := by
      rw [norm_smul (scale R u ^ 2 - scale R w ^ 2) (hessianShape R (compress R u) v),
        norm_smul (scale R w ^ 2) (hessianShape R (compress R u) v - hessianShape R (compress R w) v)]
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (scale R w))]
    _ ≤ ((2 / R) * ‖u - w‖) * ((6 / R) * ‖v‖) +
        1 * ((12 / R ^ 2) * ‖u - w‖ * ‖v‖) :=
      add_le_add (mul_le_mul (scale_square_difference R hR u w)
        (hessianShape_bound R hR _ v (compress_norm_le_radius R hR u)) (norm_nonneg _) (by positivity))
        (mul_le_mul hw hd (norm_nonneg _) zero_le_one)
    _ = _ := by ring

theorem compression_hessian_lipschitz (R : ℝ) (hR : 0 < R) :
    LipschitzWith ⟨24 / R ^ 2, by positivity⟩ (fderiv ℝ (compressDerivative (E := E) R)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u w
  simp only [dist_eq_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro t
  simp only [ContinuousLinearMap.sub_apply, actual_hessian_apply]
  have h := (hessianSlice R u t - hessianSlice R w t).le_opNorm v
  exact h.trans ((mul_le_mul_of_nonneg_right (hessianSlice_difference R hR u w t) (norm_nonneg v)).trans_eq (by simp only [NNReal.coe_mk]; ring))

theorem third_derivative_norm (R : ℝ) (hR : 0 < R) (u : E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (compress (E := E) R))) u‖ ≤ 24 / R ^ 2 := by
  have he : fderiv ℝ (compress (E := E) R) = compressDerivative R :=
    funext (fun u => (compress_hasFDerivAt R u).fderiv)
  rw [he]
  exact norm_fderiv_le_of_lipschitz ℝ (compression_hessian_lipschitz R hR)

end Bilevel.RadialWrapper
