import GradientHessian.GaussianLogSobolev

/-! Actual value and derivative bounds of exponential tilts. These
discharge the analytic premises of Gaussian log-Sobolev in Herbst's argument. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def exponentialTilt (f : E → ℝ) (t : ℝ) (x : E) : ℝ := Real.exp (t * f x)

theorem exponentialTilt_contDiff {f : E → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) :
    ContDiff ℝ 2 (exponentialTilt f t) := (contDiff_const.mul hf).exp

theorem exponentialTilt_fderiv {f : E → ℝ} (hf : Differentiable ℝ f) (t : ℝ) (x : E) :
    fderiv ℝ (exponentialTilt f t) x = Real.exp (t * f x) • (t • fderiv ℝ f x) :=
  (((hf x).hasFDerivAt.const_smul t).exp).fderiv

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem exponentialTilt_value_bounds {f : E → ℝ} {D : ℝ} (hD : ∀ x, ‖f x‖ ≤ D)
    (t : ℝ) (x : E) :
    Real.exp (-|t| * D) ≤ exponentialTilt f t x ∧
      exponentialTilt f t x ≤ Real.exp (|t| * D) := by
  have h : |t * f x| ≤ |t| * D := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hD x) (abs_nonneg t)
  have hh := abs_le.mp h
  exact ⟨Real.exp_le_exp.mpr (by linarith [hh.1]), Real.exp_le_exp.mpr hh.2⟩

theorem exponentialTilt_fderiv_bound {f : E → ℝ} {B : ℝ≥0}
    (hf : Differentiable ℝ f) (hLip : LipschitzWith B f) (t : ℝ) (x : E) :
    ‖fderiv ℝ (exponentialTilt f t) x‖ ≤ Real.exp (t * f x) * (|t| * B) := by
  rw [exponentialTilt_fderiv hf t x,
    norm_smul_of_nonneg (Real.exp_pos (t * f x)).le (t • fderiv ℝ f x),
    norm_smul t (fderiv ℝ f x), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hLip) (abs_nonneg t))
    (Real.exp_pos _).le

theorem exponentialTilt_hessian_bound {f : E → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ)) (t : ℝ) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (exponentialTilt f t)) x‖ ≤
      Real.exp (t * f x) * (|t| * C + (|t| * B) ^ 2) := by
  have hdiff := hf.differentiable (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hD : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have he : fderiv ℝ (exponentialTilt f t) = fun y =>
      exponentialTilt f t y • (t • fderiv ℝ f y) := funext (exponentialTilt_fderiv hdiff t)
  have hd := ((exponentialTilt_contDiff hf t).differentiable (by norm_num) x).hasFDerivAt.smul
    ((hD x).hasFDerivAt.const_smul t)
  rw [he, hd.fderiv]
  have h1 : ‖t • fderiv ℝ (fderiv ℝ f) x‖ ≤ |t| * (C : ℝ) := by
    calc
      _ ≤ ‖t‖ * ‖fderiv ℝ (fderiv ℝ f) x‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ _ := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hH x) (abs_nonneg t)
  have h2 : ‖t • fderiv ℝ f x‖ ≤ |t| * (B : ℝ) := by
    rw [norm_smul t (fderiv ℝ f x), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hLip) (abs_nonneg t)
  have hfirst : ‖exponentialTilt f t x • (t • fderiv ℝ (fderiv ℝ f) x)‖ ≤
      Real.exp (t * f x) * (|t| * C) := by
    calc
      _ ≤ ‖exponentialTilt f t x‖ * ‖t • fderiv ℝ (fderiv ℝ f) x‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖exponentialTilt f t x‖ * (|t| * C) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := by rw [show ‖exponentialTilt f t x‖ = Real.exp (t * f x) by
        exact Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ ‖exponentialTilt f t x • (t • fderiv ℝ (fderiv ℝ f) x)‖ +
        ‖(fderiv ℝ (exponentialTilt f t) x).smulRight (t • fderiv ℝ f x)‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ Real.exp (t * f x) * (|t| * C) +
        (Real.exp (t * f x) * (|t| * B)) * (|t| * B) := by
      apply add_le_add
      · exact hfirst
      · rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul (exponentialTilt_fderiv_bound hdiff hLip t x) h2
          (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem exponentialTilt_bounded_jets {f : E → ℝ} {B C : ℝ≥0} {D : ℝ}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (hD : ∀ x, ‖f x‖ ≤ D) (t : ℝ) :
    ∃ B' C' : ℝ≥0, LipschitzWith B' (exponentialTilt f t) ∧
      ∀ x, ‖fderiv ℝ (fderiv ℝ (exponentialTilt f t)) x‖ ≤ (C' : ℝ) := by
  let B' : ℝ≥0 := ⟨Real.exp (|t| * D) * (|t| * B), by positivity⟩
  let C' : ℝ≥0 := ⟨Real.exp (|t| * D) * (|t| * C + (|t| * B) ^ 2), by positivity⟩
  refine ⟨B', C', ?_, ?_⟩
  · apply lipschitzWith_of_nnnorm_fderiv_le
      ((exponentialTilt_contDiff hf t).differentiable (by norm_num))
    intro x
    have h := (exponentialTilt_fderiv_bound (hf.differentiable (by norm_num)) hLip t x).trans
      (mul_le_mul_of_nonneg_right (exponentialTilt_value_bounds hD t x).2 (by positivity))
    exact_mod_cast h
  · intro x
    exact (exponentialTilt_hessian_bound hf hLip hH t x).trans
      (mul_le_mul_of_nonneg_right (exponentialTilt_value_bounds hD t x).2 (by positivity))

theorem exponentialTilt_fisher_bound {f : E → ℝ} {B : ℝ≥0}
    (hf : Differentiable ℝ f) (hLip : LipschitzWith B f) (t : ℝ) (x : E) :
    ‖fderiv ℝ (exponentialTilt f t) x‖ ^ 2 / exponentialTilt f t x ≤
      t ^ 2 * (B : ℝ) ^ 2 * exponentialTilt f t x := by
  have h := exponentialTilt_fderiv_bound hf hLip t x
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  apply (div_le_iff₀ (Real.exp_pos (t * f x))).mpr
  calc
    _ ≤ (Real.exp (t * f x) * (|t| * B)) ^ 2 := hs
    _ = _ := by dsimp [exponentialTilt]; rw [mul_pow, mul_pow, sq_abs]; ring

end GradientHessian.GaussianConcentration
