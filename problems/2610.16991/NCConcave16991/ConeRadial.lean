import NCConcave16991.ConePrimitives
import NCConcave16991.LocalizationRadial
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # Actual radial protection and guard of the Section D construction -/

namespace NCConcave16991.ConeRadial

open ConePrimitives LocalizationRadial Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace

noncomputable def capSpeed (r : ℝ) : ℝ := 1 - omega (r - 2)
noncomputable def capLength (r : ℝ) : ℝ := ∫ s in (0 : ℝ)..r, capSpeed s

theorem capSpeed_contDiff : ContDiff ℝ ∞ capSpeed := by
  unfold capSpeed
  exact contDiff_const.sub (omega_contDiff.comp (by fun_prop))

theorem capLength_hasDerivAt (r : ℝ) : HasDerivAt capLength (capSpeed r) r := by
  have hc := capSpeed_contDiff.continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem capLength_contDiff : ContDiff ℝ ∞ capLength := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun r => (capLength_hasDerivAt r).differentiableAt,
    by simpa only [funext fun r => (capLength_hasDerivAt r).deriv] using capSpeed_contDiff⟩

theorem capSpeed_bounds (r : ℝ) : 0 ≤ capSpeed r ∧ capSpeed r ≤ 1 := by
  unfold capSpeed
  constructor <;> linarith [omega_nonneg (r - 2), omega_le_one (r - 2)]

theorem capSpeed_one {r : ℝ} (hr : r ≤ 2) : capSpeed r = 1 := by
  unfold capSpeed
  rw [omega_zero (by linarith : r - 2 ≤ 1 / 4)]
  ring

theorem capSpeed_zero {r : ℝ} (hr : 3 ≤ r) : capSpeed r = 0 := by
  unfold capSpeed
  rw [omega_one (by linarith : (7 / 8 : ℝ) ≤ r - 2)]
  ring

theorem capLength_identity {r : ℝ} (hr : r ≤ 2) : capLength r = r := by
  unfold capLength
  calc
    _ = ∫ _ in (0 : ℝ)..r, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact capSpeed_one (hs.2.trans (max_le (by norm_num) hr))
    _ = r := by simp

theorem capLength_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ capLength r :=
  intervalIntegral.integral_nonneg_of_forall hr (fun s => (capSpeed_bounds s).1)

theorem capLength_le_radius {r : ℝ} (hr : 0 ≤ r) : capLength r ≤ r := by
  have hh := intervalIntegral.integral_mono (μ := volume) hr
    (capSpeed_contDiff.continuous.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    (fun s => (capSpeed_bounds s).2)
  simpa [capLength] using hh

theorem capLength_constant {r : ℝ} (hr : 3 ≤ r) : capLength r = capLength 3 := by
  have hc := capSpeed_contDiff.continuous
  have hz : (∫ s in (3 : ℝ)..r, capSpeed s) = 0 := by
    calc
      _ = ∫ _ in (3 : ℝ)..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hr] at hs
        exact capSpeed_zero hs.1
      _ = 0 := by simp
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 3) (hc.intervalIntegrable 3 r)
  simpa only [capLength, hz, add_zero] using hh.symm

theorem capLength_le_three {r : ℝ} (hr : 0 ≤ r) : capLength r ≤ 3 := by
  by_cases h3 : r ≤ 3
  · exact (capLength_le_radius hr).trans h3
  · rw [capLength_constant (le_of_not_ge h3)]
    exact capLength_le_radius (by norm_num)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def radialMap (f : ℝ → ℝ) (x : E) : E := (f ‖x‖ / ‖x‖) • x

theorem radialMap_hasFDerivAt {f : ℝ → ℝ} {df : ℝ} {x : E}
    (hf : HasDerivAt f df ‖x‖) (hx : x ≠ 0) :
    HasFDerivAt (radialMap f)
      (radialOperator (unitDirection x) (f ‖x‖ / ‖x‖) df) x := by
  have hrat := hf.div (hasDerivAt_id ‖x‖) (norm_ne_zero_iff.mpr hx)
  have hh := (hrat.comp_hasFDerivAt x (norm_hasFDerivAt hx)).smul (hasFDerivAt_id (𝕜 := ℝ) x)
  refine hh.congr_fderiv ?_
  ext h
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, innerSL_apply_apply,
    radialOperator_apply, unitDirection, real_inner_smul_left, smul_smul, id_eq]
  congr 1
  field_simp

noncomputable def zeta (x : E) : E := radialMap capLength x

theorem zeta_zero : zeta (0 : E) = 0 := by simp [zeta, radialMap]

theorem zeta_identity {x : E} (hx : ‖x‖ ≤ 2) : zeta x = x := by
  by_cases hz : x = 0
  · subst x
    exact zeta_zero
  · rw [zeta, radialMap, capLength_identity hx, div_self (norm_ne_zero_iff.mpr hz), one_smul]

theorem zeta_hasFDerivAt_zero : HasFDerivAt (zeta : E → E) (ContinuousLinearMap.id ℝ E) 0 := by
  apply (hasFDerivAt_id (𝕜 := ℝ) (0 : E)).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 2)] with z hz
  exact zeta_identity (le_of_lt (by simpa using hz))

theorem zeta_differentiable : Differentiable ℝ (zeta : E → E) := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact zeta_hasFDerivAt_zero.differentiableAt
  · exact (radialMap_hasFDerivAt (capLength_hasDerivAt ‖x‖) hx).differentiableAt

theorem zeta_fderiv_norm_le (x : E) : ‖fderiv ℝ (zeta : E → E) x‖ ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    rw [zeta_hasFDerivAt_zero.fderiv]
    exact ContinuousLinearMap.norm_id_le
  · change ‖fderiv ℝ (radialMap capLength : E → E) x‖ ≤ 1
    rw [(radialMap_hasFDerivAt (capLength_hasDerivAt ‖x‖) hx).fderiv]
    apply radialOperator_norm_le _ (norm_unitDirection hx)
    · exact div_nonneg (capLength_nonneg (norm_nonneg x)) (norm_nonneg x)
    · exact (div_le_one (norm_pos_iff.mpr hx)).mpr (capLength_le_radius (norm_nonneg x))
    · exact (capSpeed_bounds _).1
    · exact (capSpeed_bounds _).2

theorem zeta_norm_bound (x : E) : ‖zeta x‖ ≤ 3 := by
  by_cases hx : x = 0
  · subst x
    rw [zeta_zero, norm_zero]
    norm_num
  · rw [zeta, radialMap, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (capLength_nonneg (norm_nonneg x)) (norm_nonneg x)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]
    exact capLength_le_three (norm_nonneg x)

noncomputable def guardSecond (M r : ℝ) : ℝ := 4 * M * omega (4 * (r - 3 / 2))
noncomputable def guardSlope (M r : ℝ) : ℝ := ∫ s in (3 / 2 : ℝ)..r, guardSecond M s
noncomputable def guardProfile (M r : ℝ) : ℝ := ∫ s in (3 / 2 : ℝ)..r, guardSlope M s
noncomputable def guard (M : ℝ) (x : E) : ℝ := guardProfile M ‖x‖

theorem guardSecond_contDiff (M : ℝ) : ContDiff ℝ ∞ (guardSecond M) := by
  unfold guardSecond
  exact contDiff_const.mul (omega_contDiff.comp (by fun_prop))

theorem guardSlope_hasDerivAt (M r : ℝ) : HasDerivAt (guardSlope M) (guardSecond M r) r := by
  have hc := (guardSecond_contDiff M).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem guardSlope_contDiff (M : ℝ) : ContDiff ℝ ∞ (guardSlope M) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun r => (guardSlope_hasDerivAt M r).differentiableAt,
    by simpa only [funext fun r => (guardSlope_hasDerivAt M r).deriv] using guardSecond_contDiff M⟩

theorem guardProfile_hasDerivAt (M r : ℝ) : HasDerivAt (guardProfile M) (guardSlope M r) r := by
  have hc := (guardSlope_contDiff M).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem guardSecond_bounds {M : ℝ} (hM : 0 ≤ M) (r : ℝ) :
    0 ≤ guardSecond M r ∧ guardSecond M r ≤ 4 * M := by
  unfold guardSecond
  constructor
  · exact mul_nonneg (by positivity) (omega_nonneg _)
  · have hh := mul_le_mul_of_nonneg_left (omega_le_one (4 * (r - 3 / 2))) (by positivity : 0 ≤ 4 * M)
    simpa using hh

theorem guardSlope_zero {M r : ℝ} (hr : r ≤ 3 / 2) : guardSlope M r = 0 := by
  unfold guardSlope
  calc
    _ = ∫ _ in (3 / 2 : ℝ)..r, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      unfold guardSecond
      rw [omega_zero (by have hh := hs.2; rw [max_eq_left hr] at hh; linarith)]
      ring
    _ = 0 := by simp

theorem guardProfile_zero {M r : ℝ} (hr : r ≤ 3 / 2) : guardProfile M r = 0 := by
  unfold guardProfile
  calc
    _ = ∫ _ in (3 / 2 : ℝ)..r, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact guardSlope_zero (by have hh := hs.2; rw [max_eq_left hr] at hh; exact hh)
    _ = 0 := by simp

theorem guardSlope_nonneg {M : ℝ} (hM : 0 ≤ M) (r : ℝ) : 0 ≤ guardSlope M r := by
  by_cases hr : r ≤ 3 / 2
  · rw [guardSlope_zero hr]
  · exact intervalIntegral.integral_nonneg_of_forall (le_of_not_ge hr) (fun s => (guardSecond_bounds hM s).1)

omit [InnerProductSpace ℝ E] in
theorem guard_nonneg {M : ℝ} (hM : 0 ≤ M) (x : E) : 0 ≤ guard M x := by
  by_cases hr : ‖x‖ ≤ 3 / 2
  · rw [guard, guardProfile_zero hr]
  · exact intervalIntegral.integral_nonneg_of_forall (le_of_not_ge hr) (guardSlope_nonneg hM)

theorem guardSlope_upper {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r) : guardSlope M r ≤ 4 * M * r := by
  by_cases hr' : r ≤ 3 / 2
  · rw [guardSlope_zero hr']
    positivity
  · have hh := intervalIntegral.integral_mono (μ := volume) (le_of_not_ge hr')
      ((guardSecond_contDiff M).continuous.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (fun s => (guardSecond_bounds hM s).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hh
    change (∫ s in (3 / 2 : ℝ)..r, guardSecond M s) ≤ _
    nlinarith

theorem guardSlope_lower {M r : ℝ} (hM : 0 ≤ M) (hr : 2 ≤ r) : M ≤ guardSlope M r := by
  have hc := (guardSecond_contDiff M).continuous
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (3 / 2) (7 / 4)) (hc.intervalIntegrable (7 / 4) r)
  have hp := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (by norm_num : (3 / 2 : ℝ) ≤ 7 / 4) (fun s => (guardSecond_bounds hM s).1)
  have he : (∫ s in (7 / 4 : ℝ)..r, guardSecond M s) = (r - 7 / 4) * (4 * M) := by
    calc
      _ = ∫ _ in (7 / 4 : ℝ)..r, (4 * M) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : (7 / 4 : ℝ) ≤ r)] at hs
        have hs0 := hs.1
        unfold guardSecond
        rw [omega_one (by linarith : (7 / 8 : ℝ) ≤ 4 * (s - 3 / 2))]
        ring
      _ = _ := by simp [smul_eq_mul]; ring
  rw [he] at hh
  change M ≤ ∫ s in (3 / 2 : ℝ)..r, guardSecond M s
  nlinarith

theorem guardProfile_contDiff (M : ℝ) : ContDiff ℝ ∞ (guardProfile M) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun r => (guardProfile_hasDerivAt M r).differentiableAt,
    by simpa only [funext fun r => (guardProfile_hasDerivAt M r).deriv] using guardSlope_contDiff M⟩

theorem guard_contDiff (M : ℝ) : ContDiff ℝ ∞ (guard M : E → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 3 / 2)] with z hz
    exact guardProfile_zero (le_of_lt (by simpa using hz))
  · exact (guardProfile_contDiff M).contDiffAt.comp x (contDiffAt_norm ℝ hx)

theorem radialOperator_norm_le_bound (u : E) (hu : ‖u‖ = 1) (a b K : ℝ)
    (hK : 0 ≤ K) (ha : 0 ≤ a) (haK : a ≤ K) (hb : 0 ≤ b) (hbK : b ≤ K) :
    ‖radialOperator u a b‖ ≤ K := by
  by_cases hK0 : K = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, hK0, radialOperator]
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    have he : radialOperator u a b = K • radialOperator u (a / K) (b / K) := by
      ext h
      simp only [smul_apply, radialOperator_apply, smul_add, smul_smul]
      congr 1 <;> field_simp
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hK]
    have hh := radialOperator_norm_le u hu (a / K) (b / K)
      (by positivity) ((div_le_one hKpos).mpr haK)
      (by positivity) ((div_le_one hKpos).mpr hbK)
    exact (mul_le_mul_of_nonneg_left hh hK).trans (by rw [mul_one])

section GuardGradient

variable [CompleteSpace E]

theorem guard_hasGradientAt (M : ℝ) (x : E) :
    HasGradientAt (guard M) (radialMap (guardSlope M) x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  by_cases hx : x = 0
  · subst x
    simp only [radialMap, norm_zero, div_zero, zero_smul, map_zero]
    apply (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (0 : E)).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 3 / 2)] with z hz
    exact guardProfile_zero (le_of_lt (by simpa using hz))
  · have hh := (guardProfile_hasDerivAt M ‖x‖).comp_hasFDerivAt x (norm_hasFDerivAt hx)
    refine hh.congr_fderiv ?_
    ext h
    simp only [smul_apply, innerSL_apply_apply, InnerProductSpace.toDual_apply_apply,
      radialMap, unitDirection, real_inner_smul_left, div_eq_mul_inv, smul_eq_mul]
    ring

theorem guard_gradient_norm {M : ℝ} (hM : 0 ≤ M) (x : E) :
    ‖gradient (guard M) x‖ = guardSlope M ‖x‖ := by
  rw [(guard_hasGradientAt M x).gradient]
  by_cases hx : x = 0
  · subst x
    simp [radialMap, guardSlope_zero (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  · rw [radialMap, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (guardSlope_nonneg hM _) (norm_nonneg x)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

theorem guard_gradient_lower {M : ℝ} (hM : 0 ≤ M) (x : E) (hx : 2 ≤ ‖x‖) :
    M ≤ ‖gradient (guard M) x‖ := by
  rw [guard_gradient_norm hM]
  exact guardSlope_lower hM hx

theorem guard_gradient_hasFDerivAt_zero (M : ℝ) :
    HasFDerivAt (𝕜 := ℝ) (gradient (guard M : E → ℝ)) 0 0 := by
  apply (hasFDerivAt_const (𝕜 := ℝ) (0 : E) (0 : E)).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 3 / 2)] with z hz
  rw [(guard_hasGradientAt M z).gradient]
  simp [radialMap, guardSlope_zero (le_of_lt (by simpa using hz))]

/-- Actual radial guard Hessian, with exactly the paper's `4M` bound. -/
theorem guard_hessian_norm_le {M : ℝ} (hM : 0 ≤ M) (x : E) :
    ‖fderiv ℝ (gradient (guard M)) x‖ ≤ 4 * M := by
  by_cases hx : x = 0
  · subst x
    rw [(guard_gradient_hasFDerivAt_zero M).fderiv, norm_zero]
    positivity
  · have he : gradient (guard M : E → ℝ) = radialMap (guardSlope M) :=
      gradient_eq (guard_hasGradientAt M)
    rw [he, (radialMap_hasFDerivAt (guardSlope_hasDerivAt M ‖x‖) hx).fderiv]
    apply radialOperator_norm_le_bound _ (norm_unitDirection hx) _ _ _ (by positivity)
    · exact div_nonneg (guardSlope_nonneg hM _) (norm_nonneg x)
    · apply (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr
      exact guardSlope_upper hM (norm_nonneg x)
    · exact (guardSecond_bounds hM _).1
    · exact (guardSecond_bounds hM _).2

/-- The concrete guard rules out an exterior block once the two actual
non-guard contributions have total norm at most `1+40*8=321`. -/
theorem guard_separation (x b : E) (hb : ‖b‖ ≤ 321)
    (hw : ‖gradient (guard 3000) x + b‖ ≤ 1 / 1000) : ‖x‖ < 2 := by
  by_contra hx
  have hl := guard_gradient_lower (by norm_num : (0 : ℝ) ≤ 3000) x (le_of_not_gt hx)
  have ht := norm_sub_le (gradient (guard 3000) x + b) b
  rw [add_sub_cancel_right] at ht
  nlinarith

end GuardGradient

end NCConcave16991.ConeRadial
