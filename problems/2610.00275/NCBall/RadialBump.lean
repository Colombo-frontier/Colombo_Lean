import NCBall.RadialCutoff

/-! # Uniform gradient and smoothness bounds for χ(x)⟨v,x⟩ -/

noncomputable section
open Set Metric Filter InnerProductSpace
open scoped Topology ContDiff InnerProductSpace
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialLinearBump (v x : E) : ℝ := radialCutoff x * ⟪v, x⟫_ℝ

def radialBumpCoefficient (v x : E) : ℝ :=
  2 * deriv radialProfile (‖x‖ ^ 2) * ⟪v, x⟫_ℝ

def radialBumpGradient (v x : E) : E :=
  radialCutoff x • v + radialBumpCoefficient v x • x

theorem radialLinearBump_smooth (v : E) : ContDiff ℝ ∞ (radialLinearBump v) :=
  radialCutoff_smooth.mul (contDiff_const.inner ℝ contDiff_id)

theorem radialBumpGradient_smooth (v : E) : ContDiff ℝ ∞ (radialBumpGradient v) :=
  (radialCutoff_smooth.smul contDiff_const).add
    ((contDiff_const.mul (radialProfile_deriv_smooth.comp (contDiff_norm_sq ℝ))).mul
      (contDiff_const.inner ℝ contDiff_id) |>.smul contDiff_id)

theorem radialBumpCoefficient_hasFDerivAt (v x : E) :
    HasFDerivAt (radialBumpCoefficient v)
      ((2 * deriv radialProfile (‖x‖ ^ 2)) • innerSL ℝ v +
        (4 * deriv (deriv radialProfile) (‖x‖ ^ 2) * ⟪v, x⟫_ℝ) • innerSL ℝ x) x := by
  have hp := (radialProfile_deriv_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
    (x := ‖x‖ ^ 2)
  have h := ((hasFDerivAt_const (2 : ℝ) x).mul
    (hp.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt)).mul
    (innerSL ℝ v).hasFDerivAt
  convert h using 1
  ext y
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, two_smul, ContinuousLinearMap.zero_apply, Function.comp_def]
  change (2 * deriv radialProfile (‖x‖ ^ 2)) * ⟪v, y⟫_ℝ +
    (4 * deriv (deriv radialProfile) (‖x‖ ^ 2) * ⟪v, x⟫_ℝ) * ⟪x, y⟫_ℝ = _
  simp only [innerSL_apply]
  ring

theorem radialBumpCoefficient_bound (v x : E) (hx : ‖x‖ ≤ 1) :
    ‖radialBumpCoefficient v x‖ ≤ 2 * radialProfileBound * ‖v‖ := by
  have hq : ‖x‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith [norm_nonneg x]⟩
  have hd := (radialProfile_derivatives_le hq).1
  have hi : ‖⟪v, x⟫_ℝ‖ ≤ ‖v‖ :=
    (norm_inner_le_norm v x).trans (by nlinarith [norm_nonneg v])
  have hA : 0 ≤ radialProfileBound := le_trans zero_le_one radialProfileBound_ge_one
  unfold radialBumpCoefficient
  rw [norm_mul (2 * deriv radialProfile (‖x‖ ^ 2)) ⟪v, x⟫_ℝ,
    norm_mul (2 : ℝ) (deriv radialProfile (‖x‖ ^ 2))]
  rw [show ‖(2 : ℝ)‖ = 2 by norm_num]
  have hprod := mul_le_mul hd hi (norm_nonneg _) hA
  nlinarith

theorem radialBumpCoefficient_fderiv_bound (v x : E) (hx : ‖x‖ ≤ 1) :
    ‖fderiv ℝ (radialBumpCoefficient v) x‖ ≤ 6 * radialProfileBound * ‖v‖ := by
  have hq : ‖x‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith [norm_nonneg x]⟩
  have hd := radialProfile_derivatives_le hq
  have hi : ‖⟪v, x⟫_ℝ‖ ≤ ‖v‖ :=
    (norm_inner_le_norm v x).trans (by nlinarith [norm_nonneg v])
  have hA : 0 ≤ radialProfileBound := le_trans zero_le_one radialProfileBound_ge_one
  rw [(radialBumpCoefficient_hasFDerivAt v x).fderiv]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul (2 * deriv radialProfile (‖x‖ ^ 2)) (innerSL ℝ v),
    norm_smul (4 * deriv (deriv radialProfile) (‖x‖ ^ 2) * ⟪v, x⟫_ℝ) (innerSL ℝ x),
    innerSL_apply_norm, innerSL_apply_norm,
    norm_mul (2 : ℝ) (deriv radialProfile (‖x‖ ^ 2)),
    norm_mul (4 * deriv (deriv radialProfile) (‖x‖ ^ 2)) ⟪v, x⟫_ℝ,
    norm_mul (4 : ℝ) (deriv (deriv radialProfile) (‖x‖ ^ 2))]
  rw [show ‖(2 : ℝ)‖ = 2 by norm_num, show ‖(4 : ℝ)‖ = 4 by norm_num]
  have hfirst := mul_le_mul_of_nonneg_right hd.1 (norm_nonneg v)
  have hprod := mul_le_mul hd.2 hi (norm_nonneg _) hA
  have hlast := mul_le_mul hprod hx (norm_nonneg x) (mul_nonneg hA (norm_nonneg v))
  nlinarith

theorem radialBumpGradient_zero (v x : E) (hx : 1 < ‖x‖) : radialBumpGradient v x = 0 := by
  have hq : 1 < ‖x‖ ^ 2 := by nlinarith
  simp [radialBumpGradient, radialCutoff_zero hx.le, radialBumpCoefficient,
    radialProfile_deriv_zero hq]

theorem radialBumpGradient_eventually_zero (v x : E) (hx : 1 < ‖x‖) :
    radialBumpGradient v =ᶠ[𝓝 x] (fun _ : E => 0) := by
  filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hx)] with y hy
  exact radialBumpGradient_zero v y hy

theorem radialBumpGradient_bound (v x : E) :
    ‖radialBumpGradient v x‖ ≤ 3 * radialProfileBound * ‖v‖ := by
  by_cases hx : ‖x‖ ≤ 1
  · have hc := radialCutoff_range x
    have hb := radialBumpCoefficient_bound v x hx
    have hA := radialProfileBound_ge_one
    have hcoef : ‖radialBumpCoefficient v x‖ * ‖x‖ ≤ 2 * radialProfileBound * ‖v‖ :=
      (mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans (by simpa using hb)
    have hcut : ‖radialCutoff x‖ * ‖v‖ ≤ ‖v‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hc.1]
      nlinarith [norm_nonneg v]
    have h := norm_add_le (radialCutoff x • v) (radialBumpCoefficient v x • x)
    simp only [norm_smul] at h
    unfold radialBumpGradient
    nlinarith [mul_le_mul_of_nonneg_right hA (norm_nonneg v)]
  · rw [radialBumpGradient_zero v x (lt_of_not_ge hx), norm_zero]
    exact mul_nonneg (by linarith [radialProfileBound_ge_one]) (norm_nonneg _)

theorem radialBumpGradient_fderiv (v x : E) :
    fderiv ℝ (radialBumpGradient v) x =
      (fderiv ℝ radialCutoff x).smulRight v +
      (radialBumpCoefficient v x • ContinuousLinearMap.id ℝ E +
        (fderiv ℝ (radialBumpCoefficient v) x).smulRight x) := by
  have hc := (radialCutoff_hasFDerivAt x).differentiableAt.hasFDerivAt
  have hb := (radialBumpCoefficient_hasFDerivAt v x).differentiableAt.hasFDerivAt
  exact ((hc.smul_const v).add (hb.smul (hasFDerivAt_id x))).fderiv

/-- A uniform Hessian bound, written as a derivative bound on the gradient. -/
theorem radialBumpGradient_fderiv_bound (v x : E) :
    ‖fderiv ℝ (radialBumpGradient v) x‖ ≤ 10 * radialProfileBound * ‖v‖ := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [radialBumpGradient_fderiv]
    have h₁ : ‖(fderiv ℝ radialCutoff x).smulRight v‖ ≤ 2 * radialProfileBound * ‖v‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (radialCutoff_fderiv_bound x) (norm_nonneg v)
    have h₂ : ‖radialBumpCoefficient v x • ContinuousLinearMap.id ℝ E‖ ≤
        2 * radialProfileBound * ‖v‖ := by
      rw [norm_smul (radialBumpCoefficient v x) (ContinuousLinearMap.id ℝ E)]
      exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans
        (by simpa using radialBumpCoefficient_bound v x hx)
    have h₃ : ‖(fderiv ℝ (radialBumpCoefficient v) x).smulRight x‖ ≤
        6 * radialProfileBound * ‖v‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact (mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans
        (by simpa using radialBumpCoefficient_fderiv_bound v x hx)
    have hsum := norm_add_le ((fderiv ℝ radialCutoff x).smulRight v)
      (radialBumpCoefficient v x • ContinuousLinearMap.id ℝ E +
        (fderiv ℝ (radialBumpCoefficient v) x).smulRight x)
    have hsum' := norm_add_le (radialBumpCoefficient v x • ContinuousLinearMap.id ℝ E)
      ((fderiv ℝ (radialBumpCoefficient v) x).smulRight x)
    linarith
  · rw [(radialBumpGradient_eventually_zero v x (lt_of_not_ge hx)).fderiv_eq, fderiv_const]
    simp only [Pi.zero_apply, norm_zero]
    exact mul_nonneg (by linarith [radialProfileBound_ge_one]) (norm_nonneg _)

theorem radialBumpGradient_lipschitz (v : E) :
    LipschitzWith ⟨10 * radialProfileBound * ‖v‖,
      mul_nonneg (by linarith [radialProfileBound_ge_one]) (norm_nonneg _)⟩ (radialBumpGradient v) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (radialBumpGradient_smooth v |>.differentiable (by simp))
  intro x
  exact radialBumpGradient_fderiv_bound v x

variable [CompleteSpace E]

theorem radialLinearBump_hasGradientAt (v x : E) :
    HasGradientAt (radialLinearBump v) (radialBumpGradient v x) x := by
  change HasFDerivAt (radialLinearBump v) (toDual ℝ E (radialBumpGradient v x)) x
  have h := (radialCutoff_hasFDerivAt x).mul (innerSL ℝ v).hasFDerivAt
  convert h using 1
  ext y
  simp [radialBumpGradient, radialBumpCoefficient, inner_add_left, inner_smul_left]
  ring

theorem radialLinearBump_gradient (v x : E) :
    gradient (radialLinearBump v) x = radialBumpGradient v x :=
  (radialLinearBump_hasGradientAt v x).gradient

theorem radialLinearBump_gradient_bound (v x : E) :
    ‖gradient (radialLinearBump v) x‖ ≤ 3 * radialProfileBound * ‖v‖ := by
  rw [radialLinearBump_gradient]
  exact radialBumpGradient_bound v x

theorem radialLinearBump_fderiv_bound (v x : E) :
    ‖fderiv ℝ (radialLinearBump v) x‖ ≤ 3 * radialProfileBound * ‖v‖ := by
  rw [(radialLinearBump_hasGradientAt v x).hasFDerivAt.fderiv, (toDual ℝ E).norm_map]
  exact radialBumpGradient_bound v x

theorem radialLinearBump_lipschitz (v : E) :
    LipschitzWith ⟨3 * radialProfileBound * ‖v‖,
      mul_nonneg (by linarith [radialProfileBound_ge_one]) (norm_nonneg _)⟩ (radialLinearBump v) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (radialLinearBump_smooth v |>.differentiable (by simp))
  intro x
  exact radialLinearBump_fderiv_bound v x

theorem radialLinearBump_smoothness (v : E) (x y : E) :
    ‖gradient (radialLinearBump v) x - gradient (radialLinearBump v) y‖ ≤
      (10 * radialProfileBound * ‖v‖) * ‖x - y‖ := by
  rw [radialLinearBump_gradient, radialLinearBump_gradient]
  simpa only [dist_eq_norm, NNReal.coe_mk] using (radialBumpGradient_lipschitz v).dist_le_mul x y

end NCBall
