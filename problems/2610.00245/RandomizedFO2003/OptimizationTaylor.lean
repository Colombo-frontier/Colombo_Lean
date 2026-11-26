import RandomizedFO2003.GradientDerivativeBounds
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace RandomizedFO2003.Calculus

open Set InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrate a power bound on the norm of a derivative along the unit
interval. This uses a differentiable scalar majorant, not an assumption
of differentiability of the norm. -/
theorem norm_at_one_le_of_deriv_power {g g' : ℝ → F} (n : ℕ) (C : ℝ)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg0 : g 0 = 0)
    (hb : ∀ t ∈ Ico (0 : ℝ) 1, ‖g' t‖ ≤ C * t ^ n) :
    ‖g 1‖ ≤ C / (n + 1) := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hg t).continuousAt)
  have hB (t : ℝ) : HasDerivAt (fun s : ℝ => C / (n + 1) * s ^ (n + 1))
      (C * t ^ n) t := by
    convert ((hasDerivAt_id t).pow (n + 1)).const_mul (C / (n + 1)) using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one]
    field_simp
    ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary hc.continuousOn
    (fun t (_ht : t ∈ Ico (0 : ℝ) 1) => (hg t).hasDerivWithinAt)
    (show ‖g 0‖ ≤ C / (n + 1) * (0 : ℝ) ^ (n + 1) by simp [hg0]) hB hb
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa using h

/-- Lipschitz derivative gives the exact quadratic linearization remainder
in any real normed spaces. No second derivative is assumed. -/
theorem norm_linearization_error_le {f : E → F} (hf : Differentiable ℝ f)
    {L : ℝ} (hlip : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖)
    (x y : E) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let g : ℝ → F := fun t => f (x + t • d) - f x - t • fderiv ℝ f x d
  let g' : ℝ → F := fun t => (fderiv ℝ f (x + t • d) - fderiv ℝ f x) d
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    have hp : HasDerivAt (fun s : ℝ => x + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have h := (((hf (x + t • d)).hasFDerivAt.comp_hasDerivAt t hp).sub_const (f x)).sub
      ((hasDerivAt_id t).smul_const (fderiv ℝ f x d))
    simpa only [g, g', Function.comp_def, ContinuousLinearMap.sub_apply, one_smul] using h
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖g' t‖ ≤ (L * ‖d‖ ^ 2) * t ^ 1 := by
    calc
      _ ≤ ‖fderiv ℝ f (x + t • d) - fderiv ℝ f x‖ * ‖d‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * ‖x + t • d - x‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right (hlip _ _) (norm_nonneg _)
      _ = _ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        ring
  have h := norm_at_one_le_of_deriv_power 1 (L * ‖d‖ ^ 2) hg (by simp [g]) hb
  convert h using 1 <;> simp [g, d]
  ring

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem norm_fderiv_sub_eq_norm_gradient_sub (f : H → ℝ) (x y : H) :
    ‖fderiv ℝ f x - fderiv ℝ f y‖ = ‖gradient f x - gradient f y‖ := by
  simpa only [map_sub, gradient] using
    ((toDual ℝ H).symm.norm_map (fderiv ℝ f x - fderiv ℝ f y)).symm

/-- The two-sided smoothness inequality, with the actual gradient. -/
theorem abs_first_order_error_le {f : H → ℝ} (hf : Differentiable ℝ f)
    {L : ℝ} (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : H) :
    |f y - f x - inner (𝕜 := ℝ) (gradient f x) (y - x)| ≤ L / 2 * ‖y - x‖ ^ 2 := by
  have hD (u v : H) : ‖fderiv ℝ f u - fderiv ℝ f v‖ ≤ L * ‖u - v‖ := by
    rw [norm_fderiv_sub_eq_norm_gradient_sub]
    exact hlip u v
  have h := norm_linearization_error_le hf hD x y
  rw [(hf x).hasGradientAt.hasFDerivAt.fderiv] at h
  simpa only [Real.norm_eq_abs, toDual_apply] using h

/-- Hessian Lipschitzness controls the gradient error of the quadratic model. -/
theorem norm_gradient_linearization_error_le {f : H → ℝ} (hf : ContDiff ℝ 2 f)
    {ρ : ℝ} (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (x y : H) :
    ‖gradient f y - gradient f x - fderiv ℝ (gradient f) x (y - x)‖ ≤ ρ / 2 * ‖y - x‖ ^ 2 :=
  norm_linearization_error_le ((gradient_contDiff 1 hf).differentiable (by norm_num)) hH x y

/-- The cubic Taylor remainder under exactly C² plus Lipschitz Hessian.
No third derivative is used. -/
theorem abs_quadratic_error_le {f : H → ℝ} (hf : ContDiff ℝ 2 f)
    {ρ : ℝ} (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (x y : H) :
    |f y - f x - inner (𝕜 := ℝ) (gradient f x) (y - x) -
      (1 / 2) * inner (𝕜 := ℝ) (fderiv ℝ (gradient f) x (y - x)) (y - x)| ≤
        ρ / 6 * ‖y - x‖ ^ 3 := by
  let d := y - x
  let a := inner (𝕜 := ℝ) (gradient f x) d
  let b := inner (𝕜 := ℝ) (fderiv ℝ (gradient f) x d) d
  let g : ℝ → ℝ := fun t => f (x + t • d) - f x - t * a - t ^ 2 / 2 * b
  let g' : ℝ → ℝ := fun t => inner (𝕜 := ℝ)
    (gradient f (x + t • d) - gradient f x - t • fderiv ℝ (gradient f) x d) d
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    have hp : HasDerivAt (fun s : ℝ => x + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hline := (hf.differentiable (by norm_num) (x + t • d)).hasGradientAt.hasFDerivAt.comp_hasDerivAt t hp
    have hd := ((hline.sub_const (f x)).sub ((hasDerivAt_id t).mul_const a)).sub
        ((((hasDerivAt_id t).pow 2).div_const 2).mul_const b)
    convert hd using 1
    simp only [g', b, a, toDual_apply, inner_sub_left, real_inner_smul_left, id_eq]
    ring
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖g' t‖ ≤ (ρ / 2 * ‖d‖ ^ 3) * t ^ 2 := by
    have he := norm_gradient_linearization_error_le hf hH x (x + t • d)
    simp only [add_sub_cancel_left, map_smul] at he
    calc
      _ ≤ ‖gradient f (x + t • d) - gradient f x - t • fderiv ℝ (gradient f) x d‖ * ‖d‖ :=
        norm_inner_le_norm _ _
      _ ≤ (ρ / 2 * ‖t • d‖ ^ 2) * ‖d‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = _ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        ring
  have h := norm_at_one_le_of_deriv_power 2 (ρ / 2 * ‖d‖ ^ 3) hg (by simp [g]) hb
  convert h using 1 <;> simp [g, d, a, b, Real.norm_eq_abs]
  ring

end InnerProduct

end RandomizedFO2003.Calculus
