import NCBall.BallRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Fundamental theorem of calculus for a Lipschitz real function

Compare differentiation under the ball average with differentiation of
its two moving endpoints. This needs no everywhere-differentiability
assumption on the original Lipschitz function.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped NNReal
namespace NCBall

theorem ballAverage_real_interval {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ) (hρ : 0 < ρ) (f : ℝ → F) (x : ℝ) :
    ballAverage volume ρ hρ f x = (2 * ρ)⁻¹ • ∫ y in (x - ρ)..(x + ρ), f y := by
  rw [ballAverage_eq_translatedIntegral, Real.volume_ball,
    ENNReal.toReal_ofReal (by positivity), Real.ball_eq_Ioo,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show x - ρ ≤ x + ρ by linarith)]

theorem ballAverage_real_hasDerivAt (ρ : ℝ) (hρ : 0 < ρ) {f : ℝ → ℝ}
    (hf : Continuous f) (x : ℝ) :
    HasDerivAt (ballAverage volume ρ hρ f)
      ((2 * ρ)⁻¹ * (f (x + ρ) - f (x - ρ))) x := by
  let A : ℝ → ℝ := fun t => ∫ y in (0 : ℝ)..t, f y
  have hA (t : ℝ) : HasDerivAt A (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have he : ballAverage volume ρ hρ f = fun y => (2 * ρ)⁻¹ * (A (y + ρ) - A (y - ρ)) := by
    funext y
    rw [ballAverage_real_interval, ← intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable 0 (y + ρ)) (hf.intervalIntegrable 0 (y - ρ))]
    rfl
  rw [he]
  have hp := (hA (x + ρ)).comp x ((hasDerivAt_id x).add_const ρ)
  have hm := (hA (x - ρ)).comp x ((hasDerivAt_id x).sub_const ρ)
  simpa only [mul_one] using (hp.sub hm).const_mul ((2 * ρ)⁻¹)

theorem integral_deriv_centered_of_lipschitz {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    (∫ t in (x - ρ)..(x + ρ), deriv f t) = f (x + ρ) - f (x - ρ) := by
  have hg := ballAverage_gradient volume ρ hρ hf x
  simp only [gradient_eq_deriv'] at hg
  rw [(ballAverage_real_hasDerivAt ρ hρ hf.continuous x).deriv] at hg
  change (2 * ρ)⁻¹ * (f (x + ρ) - f (x - ρ)) = ballAverage volume ρ hρ (deriv f) x at hg
  rw [ballAverage_real_interval, smul_eq_mul] at hg
  exact (mul_left_cancel₀ (inv_ne_zero (ne_of_gt (by positivity : 0 < 2 * ρ))) hg).symm

theorem integral_deriv_of_lipschitz {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (a b : ℝ) : (∫ t in a..b, deriv f t) = f b - f a := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · have h := integral_deriv_centered_of_lipschitz hf ((b - a) / 2) (by linarith) ((a + b) / 2)
    simpa only [show (a + b) / 2 - (b - a) / 2 = a by ring,
      show (a + b) / 2 + (b - a) / 2 = b by ring] using h
  · simp
  · have h := integral_deriv_centered_of_lipschitz hf ((a - b) / 2) (by linarith) ((b + a) / 2)
    rw [show (b + a) / 2 - (a - b) / 2 = b by ring,
      show (b + a) / 2 + (a - b) / 2 = a by ring] at h
    rw [intervalIntegral.integral_symm, h]
    ring

end NCBall
