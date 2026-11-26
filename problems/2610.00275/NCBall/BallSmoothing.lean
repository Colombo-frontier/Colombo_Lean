import NCBall.BallMeasure
import Mathlib.MeasureTheory.Function.L2Space

/-! # Lipschitz and local-gap estimates for actual ball averaging -/

noncomputable section
open MeasureTheory Set Metric
open scoped NNReal
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (τ : Measure E) [τ.IsAddHaarMeasure] (ρ : ℝ) (hρ : 0 < ρ)

theorem ballTranslate_integrable {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    Integrable (fun z => f (x + z)) (ballLaw τ ρ hρ) := by
  apply (integrable_const (‖f x‖ + (L : ℝ) * ρ)).mono'
    (hf.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  filter_upwards [ballLaw_norm_lt τ ρ hρ] with z hz
  calc
    _ ≤ ‖f (x + z) - f x‖ + ‖f x‖ := by simpa only [sub_add_cancel] using norm_add_le (f (x + z) - f x) (f x)
    _ ≤ (L : ℝ) * ‖z‖ + ‖f x‖ := by
      simpa only [add_sub_cancel_left] using add_le_add_right (hf.norm_sub_le (x + z) x) ‖f x‖
    _ ≤ _ := by nlinarith [L.coe_nonneg]

theorem ballAverage_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (ballAverage τ ρ hρ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ballAverage, ballAverage,
    ← integral_sub (ballTranslate_integrable τ ρ hρ hf x) (ballTranslate_integrable τ ρ hρ hf y)]
  have hb : ∀ᵐ z ∂ballLaw τ ρ hρ, ‖f (x + z) - f (y + z)‖ ≤ (L : ℝ) * dist x y := by
    filter_upwards [] with z
    simpa only [add_sub_add_right_eq_sub, dist_eq_norm] using hf.norm_sub_le (x + z) (y + z)
  simpa only [measureReal_univ_eq_one, mul_one] using norm_integral_le_of_norm_le_const hb

theorem ballAverage_close {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    |ballAverage τ ρ hρ f x - f x| ≤ (L : ℝ) * ρ := by
  have he : ballAverage τ ρ hρ f x - f x = ∫ z, f (x + z) - f x ∂ballLaw τ ρ hρ := by
    rw [integral_sub (ballTranslate_integrable τ ρ hρ hf x) (integrable_const _)]
    simp [ballAverage]
  rw [he, ← Real.norm_eq_abs]
  have hb : ∀ᵐ z ∂ballLaw τ ρ hρ, ‖f (x + z) - f x‖ ≤ (L : ℝ) * ρ := by
    filter_upwards [ballLaw_norm_lt τ ρ hρ] with z hz
    have hb : ‖f (x + z) - f x‖ ≤ (L : ℝ) * ‖z‖ := by
      simpa only [add_sub_cancel_left] using hf.norm_sub_le (x + z) x
    exact hb.trans (mul_le_mul_of_nonneg_left hz.le L.coe_nonneg)
  simpa only [measureReal_univ_eq_one, mul_one] using norm_integral_le_of_norm_le_const hb

theorem ballAverage_local_lower {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {x₀ x : E} {R b : ℝ} (hx : ‖x - x₀‖ + ρ ≤ R)
    (hlower : ∀ y ∈ closedBall x₀ R, b ≤ f y) : b ≤ ballAverage τ ρ hρ f x := by
  have hbound : ∀ᵐ z ∂ballLaw τ ρ hρ, b ≤ f (x + z) := by
    filter_upwards [ballLaw_norm_lt τ ρ hρ] with z hz
    apply hlower
    rw [mem_closedBall, dist_eq_norm]
    have htri : ‖x + z - x₀‖ ≤ ‖x - x₀‖ + ‖z‖ := by
      rw [show x + z - x₀ = (x - x₀) + z by abel]
      exact norm_add_le _ _
    linarith
  simpa only [integral_const, measureReal_univ_eq_one, one_smul, ballAverage] using
    integral_mono_ae (integrable_const b) (ballTranslate_integrable τ ρ hρ hf x) hbound

theorem ballAverage_local_gap {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (x₀ : E) {R Δ : ℝ} (hgap : ∀ y ∈ closedBall x₀ R, f x₀ - f y ≤ Δ)
    {x : E} (hx : ‖x - x₀‖ + ρ ≤ R) :
    ballAverage τ ρ hρ f x₀ - ballAverage τ ρ hρ f x ≤ Δ + (L : ℝ) * ρ := by
  have hl := ballAverage_local_lower τ ρ hρ hf hx (b := f x₀ - Δ)
    (fun y hy => by linarith [hgap y hy])
  have hc := (abs_le.mp (ballAverage_close τ ρ hρ hf x₀)).2
  linarith

end NCBall
