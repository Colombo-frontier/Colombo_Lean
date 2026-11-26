import NCConcave16991.ConeSmoothFunctions
import NCConcave16991.LocalizationHessian

/-! # Dimension-free Hessian bound for the actual cone radial protection -/

noncomputable section

namespace NCConcave16991.ConeSmooth

open ConePrimitives ConeRadial LocalizationRadial LocalizationHessian Set
open scoped InnerProductSpace

def capRatio (r : ℝ) : ℝ := capLength r / r

theorem capRatio_hasDerivAt {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt capRatio ((capSpeed r - capRatio r) / r) r := by
  have hh := (capLength_hasDerivAt r).div (hasDerivAt_id r) hr
  refine hh.congr_deriv ?_
  dsimp [capRatio]
  field_simp

theorem capRatio_bounds {r : ℝ} (hr : 2 ≤ r) : 0 ≤ capRatio r ∧ capRatio r ≤ 1 := by
  have hr0 : 0 < r := by linarith
  exact ⟨div_nonneg (capLength_nonneg hr0.le) hr0.le,
    (div_le_one hr0).mpr (capLength_le_radius hr0.le)⟩

theorem capRatio_deriv_bound {r : ℝ} (hr : 2 ≤ r) : |deriv capRatio r| ≤ 1 / 2 := by
  have hr0 : 0 < r := by linarith
  have ha := capRatio_bounds hr
  have hb := capSpeed_bounds r
  have hab : |capSpeed r - capRatio r| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  rw [(capRatio_hasDerivAt hr0.ne').deriv, abs_div, abs_of_pos hr0]
  exact (div_le_div_of_nonneg_right hab hr0.le).trans
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hr)

theorem capRatio_sub_bound {r s : ℝ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    |capRatio r - capRatio s| ≤ (1 / 2) * |r - s| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Ici (2 : ℝ)) (𝕜 := ℝ) (f := capRatio)
    (fun x hx ↦ (capRatio_hasDerivAt (by change 2 ≤ x at hx; linarith : x ≠ 0)).differentiableAt)
    (fun x hx ↦ by simpa only [Real.norm_eq_abs] using capRatio_deriv_bound hx)
    (convex_Ici 2) hs hr
  simpa only [Real.norm_eq_abs] using hh

theorem capSpeed_hasDerivAt (r : ℝ) : HasDerivAt capSpeed (-density (r - 2)) r := by
  have hh := ((omega_hasDerivAt (r - 2)).comp r ((hasDerivAt_id r).sub_const 2)).const_sub 1
  simp only [mul_one] at hh
  convert hh using 1
  rfl

theorem capSpeed_sub_bound (r s : ℝ) : |capSpeed r - capSpeed s| ≤ 2 * |r - s| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (𝕜 := ℝ)
    (f := capSpeed) (fun x _ ↦ (capSpeed_hasDerivAt x).differentiableAt)
    (fun x _ ↦ by
      rw [(capSpeed_hasDerivAt x).deriv, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (density_nonneg _)]
      exact density_le_two _) convex_univ (mem_univ s) (mem_univ r)
  simpa only [Real.norm_eq_abs] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem zeta_hasFDerivAt_of_ne_zero {x : E} (hx : x ≠ 0) :
    HasFDerivAt (zeta : E → E)
      (radialOperator (unitDirection x) (capRatio ‖x‖) (capSpeed ‖x‖)) x :=
  radialMap_hasFDerivAt (capLength_hasDerivAt ‖x‖) hx

theorem zeta_fderiv_identity (x : E) (hx : ‖x‖ ≤ 2) :
    fderiv ℝ (zeta : E → E) x = ContinuousLinearMap.id ℝ E := by
  by_cases hx0 : x = 0
  · subst x
    exact zeta_hasFDerivAt_zero.fderiv
  · rw [(zeta_hasFDerivAt_of_ne_zero hx0).fderiv]
    simp only [capRatio, capLength_identity hx, div_self (norm_ne_zero_iff.mpr hx0), capSpeed_one hx]
    simp [radialOperator]

theorem zeta_fderiv_sub_bound_outside (x y : E) (hx : 2 ≤ ‖x‖) (hy : 2 ≤ ‖y‖) :
    ‖fderiv ℝ (zeta : E → E) x - fderiv ℝ (zeta : E → E) y‖ ≤ 5 * ‖x - y‖ := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖x‖)
  have hy0 : y ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖y‖)
  rw [(zeta_hasFDerivAt_of_ne_zero hx0).fderiv, (zeta_hasFDerivAt_of_ne_zero hy0).fderiv]
  have hab := radialOperator_sub_bound (unitDirection x) (unitDirection y)
    (norm_unitDirection hx0) (norm_unitDirection hy0)
    (capRatio ‖x‖) (capSpeed ‖x‖) (capRatio ‖y‖) (capSpeed ‖y‖)
    (capRatio_bounds hy).1 (capRatio_bounds hy).2 (capSpeed_bounds ‖y‖).1 (capSpeed_bounds ‖y‖).2
  have ha := capRatio_sub_bound hx hy
  have hb := capSpeed_sub_bound ‖x‖ ‖y‖
  have hu := unitDirection_sub_bound (by norm_num : (0 : ℝ) < 2) x y hx hy
  have hn := abs_norm_sub_norm_le x y
  have hA := mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hB := mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at hu
  nlinarith

theorem zeta_fderiv_sub_bound_mixed (x y : E) (hx : ‖x‖ ≤ 2) (hy : 2 ≤ ‖y‖) :
    ‖fderiv ℝ (zeta : E → E) x - fderiv ℝ (zeta : E → E) y‖ ≤ 5 * ‖x - y‖ := by
  have hy0 : y ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖y‖)
  let z : E := (2 : ℝ) • unitDirection y
  have hz : ‖z‖ = 2 := by simp [z, norm_smul, Real.norm_eq_abs, norm_unitDirection hy0]
  have hdist : ‖z - y‖ = ‖y‖ - 2 := by
    have he : z - y = (2 / ‖y‖ - 1) • y := by
      simp only [z, unitDirection, smul_smul, div_eq_mul_inv, sub_smul, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonpos
      (sub_nonpos.mpr ((div_le_one (by linarith : 0 < ‖y‖)).mpr hy))]
    field_simp
    ring
  rw [zeta_fderiv_identity x hx, ← zeta_fderiv_identity z hz.le]
  have hh := zeta_fderiv_sub_bound_outside z y hz.ge hy
  rw [hdist] at hh
  have hn := norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hn
  exact hh.trans (by nlinarith)

theorem zeta_fderiv_sub_bound (x y : E) :
    ‖fderiv ℝ (zeta : E → E) x - fderiv ℝ (zeta : E → E) y‖ ≤ 5 * ‖x - y‖ := by
  by_cases hx : ‖x‖ ≤ 2
  · by_cases hy : ‖y‖ ≤ 2
    · rw [zeta_fderiv_identity x hx, zeta_fderiv_identity y hy, sub_self, norm_zero]
      positivity
    · exact zeta_fderiv_sub_bound_mixed x y hx (le_of_not_ge hy)
  · by_cases hy : ‖y‖ ≤ 2
    · simpa only [norm_sub_rev] using zeta_fderiv_sub_bound_mixed y x hy (le_of_not_ge hx)
    · exact zeta_fderiv_sub_bound_outside x y (le_of_not_ge hx) (le_of_not_ge hy)

theorem zeta_hessian_norm_le (x : E) : ‖fderiv ℝ (fderiv ℝ (zeta : E → E)) x‖ ≤ 5 :=
  norm_fderiv_le_of_lip' (𝕜 := ℝ) (by norm_num : (0 : ℝ) ≤ 5)
    (Filter.Eventually.of_forall (fun y ↦ zeta_fderiv_sub_bound y x))

theorem zeta_sub_bound (x y : E) : ‖zeta x - zeta y‖ ≤ ‖x - y‖ := by
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (𝕜 := ℝ)
    (f := (zeta : E → E)) (fun z _ ↦ zeta_differentiable z)
    (fun z _ ↦ zeta_fderiv_norm_le z) convex_univ (mem_univ y) (mem_univ x)
  simpa only [one_mul] using hh

end NCConcave16991.ConeSmooth
