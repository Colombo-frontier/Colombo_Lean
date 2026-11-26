import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# An explicit radial cutoff with dimension-independent derivative constants

The scalar profile is fixed once, before choosing an inner product space. This
avoids a dimension-dependent choice of a generic bump function.
-/

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff InnerProductSpace
namespace NCBall

def radialProfile (t : ℝ) : ℝ := Real.smoothTransition ((16 / 15) * (1 - t))

theorem radialProfile_smooth : ContDiff ℝ ∞ radialProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

theorem radialProfile_deriv_smooth : ContDiff ℝ ∞ (deriv radialProfile) :=
  (contDiff_infty_iff_deriv.mp radialProfile_smooth).2

theorem radialProfile_deriv2_smooth : ContDiff ℝ ∞ (deriv (deriv radialProfile)) :=
  (contDiff_infty_iff_deriv.mp radialProfile_deriv_smooth).2

theorem radialProfile_range (t : ℝ) : 0 ≤ radialProfile t ∧ radialProfile t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem radialProfile_one {t : ℝ} (ht : t ≤ 1 / 16) : radialProfile t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem radialProfile_zero {t : ℝ} (ht : 1 ≤ t) : radialProfile t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem radialProfile_deriv_zero {t : ℝ} (ht : 1 < t) : deriv radialProfile t = 0 := by
  have heq : radialProfile =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact radialProfile_zero hs.le
  rw [heq.deriv_eq, deriv_const]

theorem exists_radialProfile_derivative_bound : ∃ A : ℝ, 1 ≤ A ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv radialProfile t‖ ≤ A ∧
      ‖deriv (deriv radialProfile) t‖ ≤ A := by
  obtain ⟨A₁, hA₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    radialProfile_deriv_smooth.continuous.continuousOn
  obtain ⟨A₂, hA₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    radialProfile_deriv2_smooth.continuous.continuousOn
  refine ⟨max 1 (max A₁ A₂), le_max_left _ _, ?_⟩
  intro t ht
  exact ⟨(hA₁ t ht).trans ((le_max_left A₁ A₂).trans (le_max_right _ _)),
    (hA₂ t ht).trans ((le_max_right A₁ A₂).trans (le_max_right _ _))⟩

def radialProfileBound : ℝ := Classical.choose exists_radialProfile_derivative_bound

theorem radialProfileBound_ge_one : 1 ≤ radialProfileBound :=
  (Classical.choose_spec exists_radialProfile_derivative_bound).1

def bumpConstant : ℝ := 10 * radialProfileBound

theorem bumpConstant_ge_one : 1 ≤ bumpConstant := by
  unfold bumpConstant
  linarith [radialProfileBound_ge_one]

theorem bumpConstant_pos : 0 < bumpConstant := lt_of_lt_of_le zero_lt_one bumpConstant_ge_one

theorem radialProfile_derivatives_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖deriv radialProfile t‖ ≤ radialProfileBound ∧
      ‖deriv (deriv radialProfile) t‖ ≤ radialProfileBound :=
  (Classical.choose_spec exists_radialProfile_derivative_bound).2 t ht

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialCutoff (x : E) : ℝ := radialProfile (‖x‖ ^ 2)

theorem radialCutoff_smooth : ContDiff ℝ ∞ (radialCutoff : E → ℝ) :=
  radialProfile_smooth.comp (contDiff_norm_sq ℝ)

omit [InnerProductSpace ℝ E] in
theorem radialCutoff_range (x : E) : 0 ≤ radialCutoff x ∧ radialCutoff x ≤ 1 :=
  radialProfile_range _

omit [InnerProductSpace ℝ E] in
theorem radialCutoff_one {x : E} (hx : ‖x‖ ≤ 1 / 4) : radialCutoff x = 1 := by
  apply radialProfile_one
  nlinarith [norm_nonneg x]

omit [InnerProductSpace ℝ E] in
theorem radialCutoff_zero {x : E} (hx : 1 ≤ ‖x‖) : radialCutoff x = 0 := by
  apply radialProfile_zero
  nlinarith

omit [InnerProductSpace ℝ E] in
theorem radialCutoff_eventually_zero {x : E} (hx : 1 < ‖x‖) :
    radialCutoff =ᶠ[𝓝 x] (fun _ : E => 0) := by
  filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hx)] with y hy
  exact radialCutoff_zero hy.le

theorem radialCutoff_hasFDerivAt (x : E) :
    HasFDerivAt radialCutoff ((2 * deriv radialProfile (‖x‖ ^ 2)) • innerSL ℝ x) x := by
  have hp := (radialProfile_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
    (x := ‖x‖ ^ 2)
  have h := hp.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  convert h using 1
  ext y
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, two_smul,
    ContinuousLinearMap.add_apply]
  ring

theorem radialCutoff_fderiv (x : E) :
    fderiv ℝ radialCutoff x = (2 * deriv radialProfile (‖x‖ ^ 2)) • innerSL ℝ x :=
  (radialCutoff_hasFDerivAt x).fderiv

/-- The constant is independent of E, hence of its dimension. -/
theorem radialCutoff_fderiv_bound (x : E) :
    ‖fderiv ℝ radialCutoff x‖ ≤ 2 * radialProfileBound := by
  by_cases hx : ‖x‖ ≤ 1
  · have hq : ‖x‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith [norm_nonneg x]⟩
    have hd := (radialProfile_derivatives_le hq).1
    rw [radialCutoff_fderiv]
    change ‖((2 * deriv radialProfile (‖x‖ ^ 2)) • innerSL ℝ x : E →L[ℝ] ℝ)‖ ≤
      2 * radialProfileBound
    rw [norm_smul (2 * deriv radialProfile (‖x‖ ^ 2)) (innerSL ℝ x),
      norm_mul, innerSL_apply_norm]
    rw [show ‖(2 : ℝ)‖ = 2 by norm_num]
    have hA := radialProfileBound_ge_one
    nlinarith [norm_nonneg (deriv radialProfile (‖x‖ ^ 2)),
      mul_le_mul hd hx (norm_nonneg x) (by linarith : 0 ≤ radialProfileBound)]
  · rw [(radialCutoff_eventually_zero (lt_of_not_ge hx)).fderiv_eq, fderiv_const]
    simp only [Pi.zero_apply, norm_zero]
    linarith [radialProfileBound_ge_one]

end NCBall
