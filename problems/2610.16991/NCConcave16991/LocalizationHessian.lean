import NCConcave16991.LocalizationRadial
import NCConcave16991.LocalizationStep

/-!
# Dimension-free Hessian estimate for the actual radial cap

The Jacobian is compared through its radial/tangential decomposition. The
scalar profile and exponential derivative estimates are already proved for
the actual integral cutoff. No bound on a cap derivative is assumed here.
-/

namespace NCConcave16991.LocalizationHessian

open LocalizationScalar LocalizationRadial LocalizationStep Set
open scoped InnerProductSpace Topology

noncomputable def ratio (C r : ℝ) : ℝ := radialLength C r / r

theorem ratio_hasDerivAt (C : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (ratio C) ((radialSpeed C r - ratio C r) / r) r := by
  have hh := (radialLength_hasDerivAt C r).div (hasDerivAt_id r) hr
  refine hh.congr_deriv ?_
  dsimp [ratio]
  field_simp

theorem ratio_bounds {C r : ℝ} (hC : 0 < C) (hr : C ≤ r) :
    0 ≤ ratio C r ∧ ratio C r ≤ 1 := by
  have hr0 := hC.trans_le hr
  exact ⟨div_nonneg (radialLength_nonneg hr0.le) hr0.le,
    (div_le_one hr0).mpr (radialLength_le_radius hr0.le)⟩

theorem ratio_deriv_bound {C r : ℝ} (hC : 0 < C) (hr : C ≤ r) :
    |deriv (ratio C) r| ≤ 1 / C := by
  have hr0 := hC.trans_le hr
  have ha := ratio_bounds hC hr
  have hb0 := radialSpeed_nonneg C r
  have hb1 := radialSpeed_le_one C r
  have hab : |radialSpeed C r - ratio C r| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  rw [(ratio_hasDerivAt C hr0.ne').deriv, abs_div, abs_of_pos hr0]
  exact (div_le_div_of_nonneg_right hab hr0.le).trans
    (one_div_le_one_div_of_le hC hr)

theorem ratio_sub_bound {C r s : ℝ} (hC : 0 < C) (hr : C ≤ r) (hs : C ≤ s) :
    |ratio C r - ratio C s| ≤ (1 / C) * |r - s| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Ici C) (𝕜 := ℝ) (f := ratio C)
    (fun x hx => (ratio_hasDerivAt C (hC.trans_le hx).ne').differentiableAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using ratio_deriv_bound hC hx)
    (convex_Ici C) hs hr
  simpa only [Real.norm_eq_abs] using hh

theorem speed_sub_bound {C : ℝ} (hC : 0 < C) (r s : ℝ) :
    |radialSpeed C r - radialSpeed C s| ≤ (8 / C) * |r - s| := by
  have hbound (x : ℝ) : ‖deriv (radialSpeed C) x‖ ≤ 8 / C := by
    rw [(radialSpeed_hasDerivAt C x).deriv, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos hC, abs_of_nonneg (step_deriv_bounds _).1]
    exact div_le_div_of_nonneg_right (step_deriv_bounds _).2 hC.le
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (𝕜 := ℝ)
    (f := radialSpeed C) (fun x _ => (radialSpeed_hasDerivAt C x).differentiableAt)
    (fun x _ => hbound x) convex_univ (mem_univ s) (mem_univ r)
  simpa only [Real.norm_eq_abs] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def rankProjection (u : E) : E →L[ℝ] E := (innerSL ℝ u).smulRight u

theorem rankProjection_norm (u : E) : ‖rankProjection u‖ = ‖u‖ ^ 2 := by
  rw [rankProjection, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, pow_two]

theorem rankProjection_sub_bound (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖rankProjection u - rankProjection v‖ ≤ 2 * ‖u - v‖ := by
  have he : rankProjection u - rankProjection v =
      (innerSL ℝ (u - v)).smulRight u + (innerSL ℝ v).smulRight (u - v) := by
    ext h
    simp only [rankProjection, sub_apply, add_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_sub_left, sub_smul, smul_sub]
    abel
  rw [he]
  have hh := norm_add_le ((innerSL ℝ (u - v)).smulRight u)
    ((innerSL ℝ v).smulRight (u - v))
  simpa only [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, hu, hv,
    mul_one, one_mul, two_mul] using hh

theorem radialOperator_sub_bound (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (a b c d : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    ‖radialOperator u a b - radialOperator v c d‖ ≤
      2 * |a - c| + |b - d| + 2 * ‖u - v‖ := by
  have hdc : |d - c| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have he : radialOperator u a b - radialOperator v c d =
      (a - c) • ContinuousLinearMap.id ℝ E + ((b - d) - (a - c)) • rankProjection u +
        (d - c) • (rankProjection u - rankProjection v) := by
    ext h
    simp only [radialOperator, rankProjection, add_apply, sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, sub_smul, smul_sub]
    abel
  rw [he]
  have hnorm := norm_add_le
    ((a - c) • ContinuousLinearMap.id ℝ E + ((b - d) - (a - c)) • rankProjection u)
    ((d - c) • (rankProjection u - rankProjection v))
  have hnorm2 := norm_add_le ((a - c) • ContinuousLinearMap.id ℝ E)
    (((b - d) - (a - c)) • rankProjection u)
  simp only [norm_smul, Real.norm_eq_abs, rankProjection_norm, hu, one_pow, mul_one] at hnorm hnorm2
  have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
  have hi := mul_le_mul_of_nonneg_left hid (abs_nonneg (a - c))
  have hcoeff := abs_sub (b - d) (a - c)
  have hrank := rankProjection_sub_bound u v hu hv
  have hprod := mul_le_mul hdc hrank (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

theorem unitDirection_sub_bound {C : ℝ} (hC : 0 < C) (x y : E)
    (hx : C ≤ ‖x‖) (hy : C ≤ ‖y‖) :
    ‖unitDirection x - unitDirection y‖ ≤ (2 / C) * ‖x - y‖ := by
  have hr := hC.trans_le hx
  have hs := hC.trans_le hy
  have he : unitDirection x - unitDirection y =
      ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by
    simp only [unitDirection, smul_sub, sub_smul]
    abel
  have hn : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    rw [inv_sub_inv hr.ne' hs.ne', abs_div, abs_mul, abs_of_pos hr, abs_of_pos hs]
    field_simp
  rw [he]
  have htri := norm_add_le (‖x‖⁻¹ • (x - y)) ((‖x‖⁻¹ - ‖y‖⁻¹) • y)
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hn] at htri
  have hdist := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hdist
  have hh := div_le_div_of_nonneg_right hdist hr.le
  have hrec := one_div_le_one_div_of_le hC hx
  have hmul := mul_le_mul_of_nonneg_right hrec (norm_nonneg (x - y))
  simp only [div_eq_mul_inv, one_mul] at hh hmul htri ⊢
  nlinarith

theorem radialCap_fderiv_sub_bound_outside {C : ℝ} (hC : 0 < C) (x y : E)
    (hx : C ≤ ‖x‖) (hy : C ≤ ‖y‖) :
    ‖fderiv ℝ (radialCap C) x - fderiv ℝ (radialCap C) y‖ ≤ (14 / C) * ‖x - y‖ := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hC.trans_le hx)
  have hy0 : y ≠ 0 := norm_pos_iff.mp (hC.trans_le hy)
  rw [(radialCap_hasFDerivAt_of_ne_zero hx0).fderiv,
    (radialCap_hasFDerivAt_of_ne_zero hy0).fderiv]
  have hab := radialOperator_sub_bound (unitDirection x) (unitDirection y)
    (norm_unitDirection hx0) (norm_unitDirection hy0)
    (ratio C ‖x‖) (radialSpeed C ‖x‖) (ratio C ‖y‖) (radialSpeed C ‖y‖)
    (ratio_bounds hC hy).1 (ratio_bounds hC hy).2
    (radialSpeed_nonneg C ‖y‖) (radialSpeed_le_one C ‖y‖)
  have ha := ratio_sub_bound hC hx hy
  have hb := speed_sub_bound hC ‖x‖ ‖y‖
  have hu := unitDirection_sub_bound hC x y hx hy
  have hn := abs_norm_sub_norm_le x y
  have hA := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 1 / C)
  have hB := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 8 / C)
  change ‖radialOperator (unitDirection x) (ratio C ‖x‖) (radialSpeed C ‖x‖) -
    radialOperator (unitDirection y) (ratio C ‖y‖) (radialSpeed C ‖y‖)‖ ≤ _
  have hcoeff : 2 * (1 / C) + 8 / C + 2 * (2 / C) = 14 / C := by ring
  simp only [div_eq_mul_inv, one_mul] at ha hb hu hA hB hcoeff ⊢
  nlinarith

theorem radialCap_fderiv_identity {C : ℝ} (hC : 0 < C) (x : E) (hx : ‖x‖ ≤ C) :
    fderiv ℝ (radialCap C) x = ContinuousLinearMap.id ℝ E := by
  by_cases hx0 : x = 0
  · subst x
    exact (radialCap_hasFDerivAt_zero hC).fderiv
  · rw [(radialCap_hasFDerivAt_of_ne_zero hx0).fderiv,
      radialLength_identity hC hx, div_self (norm_ne_zero_iff.mpr hx0), radialSpeed_one hC hx]
    simp [radialOperator]

theorem radialCap_fderiv_sub_bound_mixed {C : ℝ} (hC : 0 < C) (x y : E)
    (hx : ‖x‖ ≤ C) (hy : C ≤ ‖y‖) :
    ‖fderiv ℝ (radialCap C) x - fderiv ℝ (radialCap C) y‖ ≤ (14 / C) * ‖x - y‖ := by
  have hy0 : y ≠ 0 := norm_pos_iff.mp (hC.trans_le hy)
  let z : E := C • unitDirection y
  have hz : ‖z‖ = C := by simp [z, norm_smul, Real.norm_eq_abs, abs_of_pos hC, norm_unitDirection hy0]
  have hdist : ‖z - y‖ = ‖y‖ - C := by
    have he : z - y = (C / ‖y‖ - 1) • y := by
      simp only [z, unitDirection, smul_smul, div_eq_mul_inv, sub_smul, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonpos
      (by exact sub_nonpos.mpr ((div_le_one (hC.trans_le hy)).mpr hy))]
    field_simp
    ring
  rw [radialCap_fderiv_identity hC x hx,
    ← radialCap_fderiv_identity hC z hz.le]
  have hh := radialCap_fderiv_sub_bound_outside hC z y hz.ge hy
  rw [hdist] at hh
  have hn := norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hn
  have hm := mul_le_mul_of_nonneg_left (show ‖y‖ - C ≤ ‖x - y‖ by linarith)
    (by positivity : 0 ≤ 14 / C)
  exact hh.trans hm

/-- Actual global Jacobian Lipschitz bound, sharper than the source's 18/C. -/
theorem radialCap_fderiv_sub_bound {C : ℝ} (hC : 0 < C) (x y : E) :
    ‖fderiv ℝ (radialCap C) x - fderiv ℝ (radialCap C) y‖ ≤ (14 / C) * ‖x - y‖ := by
  by_cases hx : ‖x‖ ≤ C
  · by_cases hy : ‖y‖ ≤ C
    · rw [radialCap_fderiv_identity hC x hx, radialCap_fderiv_identity hC y hy, sub_self, norm_zero]
      positivity
    · exact radialCap_fderiv_sub_bound_mixed hC x y hx (le_of_not_ge hy)
  · by_cases hy : ‖y‖ ≤ C
    · simpa only [norm_sub_rev] using
        radialCap_fderiv_sub_bound_mixed hC y x hy (le_of_not_ge hx)
    · exact radialCap_fderiv_sub_bound_outside hC x y (le_of_not_ge hx) (le_of_not_ge hy)

/-- The actual second Fréchet derivative of the explicit smooth cap has
dimension-free operator norm at most the paper's 18/C. -/
theorem radialCap_hessian_norm_le {C : ℝ} (hC : 0 < C) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (radialCap C)) x‖ ≤ 18 / C := by
  apply (norm_fderiv_le_of_lip' (𝕜 := ℝ) (by positivity : 0 ≤ 14 / C)
    (Filter.Eventually.of_forall (fun y => radialCap_fderiv_sub_bound hC y x))).trans
  exact div_le_div_of_nonneg_right (by norm_num : (14 : ℝ) ≤ 18) hC.le

theorem radialCap_jacobian_hasFDerivAt {C : ℝ} (hC : 0 < C) (x : E) :
    HasFDerivAt (fderiv ℝ (radialCap C)) (fderiv ℝ (fderiv ℝ (radialCap C)) x) x := by
  have hc : ContDiff ℝ 1 (fderiv ℝ (radialCap C : E → E)) :=
    (radialCap_contDiff hC).fderiv_right (by simp)
  exact (hc.differentiable one_ne_zero x).hasFDerivAt

theorem radialScore_fderiv {C : ℝ} (hC : 0 < C) (u x : E) :
    fderiv ℝ (fun z => ⟪u, radialCap C z⟫_ℝ) x =
      (innerSL ℝ u).comp (fderiv ℝ (radialCap C) x) := by
  exact ((innerSL ℝ u).hasFDerivAt.comp x
    (radialCap_differentiable hC x).hasFDerivAt).fderiv

theorem radialScore_fderiv_norm_le {C : ℝ} (hC : 0 < C) (u : E) (hu : ‖u‖ = 1) (x : E) :
    ‖fderiv ℝ (fun z => ⟪u, radialCap C z⟫_ℝ) x‖ ≤ 1 := by
  rw [radialScore_fderiv hC]
  have hh := (innerSL ℝ u).opNorm_comp_le (fderiv ℝ (radialCap C) x)
  rw [innerSL_apply_norm, hu, one_mul] at hh
  exact hh.trans (radialCap_fderiv_norm_le hC x)

theorem radialScore_fderiv_sub_bound {C : ℝ} (hC : 0 < C) (u : E) (hu : ‖u‖ = 1) (x y : E) :
    ‖fderiv ℝ (fun z => ⟪u, radialCap C z⟫_ℝ) x -
      fderiv ℝ (fun z => ⟪u, radialCap C z⟫_ℝ) y‖ ≤ (14 / C) * ‖x - y‖ := by
  rw [radialScore_fderiv hC, radialScore_fderiv hC]
  have he : (innerSL ℝ u).comp (fderiv ℝ (radialCap C) x) -
      (innerSL ℝ u).comp (fderiv ℝ (radialCap C) y) =
      (innerSL ℝ u).comp (fderiv ℝ (radialCap C) x - fderiv ℝ (radialCap C) y) := by
    ext h
    simp
  rw [he]
  have hh := (innerSL ℝ u).opNorm_comp_le
    (fderiv ℝ (radialCap C) x - fderiv ℝ (radialCap C) y)
  rw [innerSL_apply_norm, hu, one_mul] at hh
  exact hh.trans (radialCap_fderiv_sub_bound hC x y)

theorem radialScore_hessian_norm_le {C : ℝ} (hC : 0 < C) (u : E) (hu : ‖u‖ = 1) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun z => ⟪u, radialCap C z⟫_ℝ)) x‖ ≤ 18 / C := by
  apply (norm_fderiv_le_of_lip' (𝕜 := ℝ) (by positivity : 0 ≤ 14 / C)
    (Filter.Eventually.of_forall (fun y => radialScore_fderiv_sub_bound hC u hu y x))).trans
  exact div_le_div_of_nonneg_right (by norm_num : (14 : ℝ) ≤ 18) hC.le

/-- The state score bounds used in global admissibility for `Z=rho_10`. -/
theorem paper_state_score_bounds (u : E) (hu : ‖u‖ = 1) (x : E) :
    ‖fderiv ℝ (fun z => ⟪u, radialCap 10 z⟫_ℝ) x‖ ≤ 1 ∧
      ‖fderiv ℝ (fderiv ℝ (fun z => ⟪u, radialCap 10 z⟫_ℝ)) x‖ ≤ 2 := by
  constructor
  · exact radialScore_fderiv_norm_le (by norm_num) u hu x
  · exact (radialScore_hessian_norm_le (by norm_num : (0 : ℝ) < 10) u hu x).trans (by norm_num)

/-- The connector cap bound used in global admissibility for `E_nu=rho_21`. -/
theorem paper_connector_cap_hessian_bound (x : E) :
    ‖fderiv ℝ (fderiv ℝ (radialCap 21)) x‖ ≤ 1 :=
  (radialCap_hessian_norm_le (by norm_num : (0 : ℝ) < 21) x).trans (by norm_num)

end NCConcave16991.LocalizationHessian
