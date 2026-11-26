import RandomizedFO2003.OptimizationTaylor
import RandomizedFO2003.Model

namespace RandomizedFO2003.Accelerated

open InnerProductSpace
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def extrapolate (θ : ℝ) (previous current : E) : E := current + (1 - θ) • (current - previous)

noncomputable def gradientStep (η : ℝ) (f : E → ℝ) (y : E) : E := y - η • gradient f y

theorem gradient_step_decrease {f : E → ℝ} (hf : Differentiable ℝ f)
    {L η : ℝ} (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hη : 0 ≤ η) (hstep : L * η ≤ 1 / 4) (y : E) :
    f (gradientStep η f y) ≤ f y - (7 * η / 8) * ‖gradient f y‖ ^ 2 := by
  have hs := (abs_le.mp (Calculus.abs_first_order_error_le hf hlip y (gradientStep η f y))).2
  have hd : gradientStep η f y - y = -(η • gradient f y) := by
    unfold gradientStep
    abel
  rw [hd, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hs
  have hq := mul_le_mul_of_nonneg_right hstep (mul_nonneg hη (sq_nonneg ‖gradient f y‖))
  nlinarith

/-- A gradient step from an arbitrary extrapolated point. The scaled form
retains exactly the constants needed when summing an accelerated epoch. -/
theorem step_energy_scaled {f : E → ℝ} (hf : Differentiable ℝ f)
    {L η : ℝ} (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hη : 0 ≤ η) (hstep : L * η ≤ 1 / 4) (x y : E) :
    8 * η * (f (gradientStep η f y) - f x) ≤
      5 * ‖x - y‖ ^ 2 - 4 * ‖gradientStep η f y - x‖ ^ 2 - 3 * η ^ 2 * ‖gradient f y‖ ^ 2 := by
  have hdec := gradient_step_decrease hf hlip hη hstep y
  have hlo := (abs_le.mp (Calculus.abs_first_order_error_le hf hlip y x)).1
  have hnorm := norm_sub_sq_real (y - x) (η • gradient f y)
  have hz : y - x - η • gradient f y = gradientStep η f y - x := by
    unfold gradientStep
    abel
  rw [hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη, real_inner_smul_right,
    real_inner_comm (gradient f y) (y - x), norm_sub_rev y x] at hnorm
  have hin : inner (𝕜 := ℝ) (gradient f y) (y - x) =
      -inner (𝕜 := ℝ) (gradient f y) (x - y) := by rw [← inner_neg_right, neg_sub]
  rw [hin] at hnorm
  have hdec' := mul_le_mul_of_nonneg_left hdec (show 0 ≤ 8 * η by positivity)
  have hlo' := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 8 * η by positivity)
  have hq := mul_le_mul_of_nonneg_right hstep (sq_nonneg ‖x - y‖)
  nlinarith

omit [CompleteSpace E] in
theorem extrapolate_displacement_le {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (p x : E) :
    ‖x - extrapolate θ p x‖ ≤ ‖x - p‖ := by
  have he : x - extrapolate θ p x = -((1 - θ) • (x - p)) := by
    unfold extrapolate
    abel
  rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ1)]
  nlinarith [norm_nonneg (x - p)]

theorem accelerated_step_energy_scaled {f : E → ℝ} (hf : Differentiable ℝ f)
    {L η θ : ℝ} (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hη : 0 ≤ η) (hstep : L * η ≤ 1 / 4) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (p x : E) :
    let y := extrapolate θ p x
    let z := gradientStep η f y
    8 * η * (f z - f x) ≤ 5 * ‖x - p‖ ^ 2 - 4 * ‖z - x‖ ^ 2 -
      3 * η ^ 2 * ‖gradient f y‖ ^ 2 := by
  have hs := step_energy_scaled hf hlip hη hstep x (extrapolate θ p x)
  have hn := extrapolate_displacement_le hθ hθ1 p x
  have hn2 := sq_le_sq₀ (norm_nonneg (x - extrapolate θ p x)) (norm_nonneg (x - p))
  nlinarith [hn2.mpr hn]

end RandomizedFO2003.Accelerated
