import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # The actual normalized Haar measure on a positive-radius ball -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def ballLaw (τ : Measure E) (ρ : ℝ) (_hρ : 0 < ρ) : Measure E := cond τ (ball 0 ρ)

instance ballLaw_probability (τ : Measure E) [τ.IsAddHaarMeasure] (ρ : ℝ) (hρ : 0 < ρ) :
    IsProbabilityMeasure (ballLaw τ ρ hρ) :=
  cond_isProbabilityMeasure_of_finite (measure_ball_pos τ 0 hρ).ne' measure_ball_lt_top.ne

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem ballLaw_absolutelyContinuous (τ : Measure E) (ρ : ℝ) (hρ : 0 < ρ) :
    ballLaw τ ρ hρ ≪ τ := cond_absolutelyContinuous

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem ballLaw_norm_lt (τ : Measure E) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᵐ z ∂ballLaw τ ρ hρ, ‖z‖ < ρ := by
  simpa only [mem_ball, dist_zero_right] using
    ae_cond_mem (μ := τ) (s := ball (0 : E) ρ) isOpen_ball.measurableSet

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem ballLaw_shift_mem (τ : Measure E) (ρ : ℝ) (hρ : 0 < ρ) (x : E) :
    ∀ᵐ z ∂ballLaw τ ρ hρ, x + z ∈ closedBall x ρ := by
  filter_upwards [ballLaw_norm_lt τ ρ hρ] with z hz
  simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hz.le

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def ballAverage (τ : Measure E) (ρ : ℝ) (hρ : 0 < ρ) (f : E → F) (x : E) : F :=
  ∫ z, f (x + z) ∂ballLaw τ ρ hρ

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem ballAverage_eq_setIntegral (τ : Measure E) (ρ : ℝ) (hρ : 0 < ρ) (f : E → F) (x : E) :
    ballAverage τ ρ hρ f x = (τ (ball (0 : E) ρ)).toReal⁻¹ • ∫ z in ball 0 ρ, f (x + z) ∂τ := by
  rw [ballAverage, ballLaw, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem setIntegral_ball_translate (τ : Measure E) [τ.IsAddHaarMeasure] (ρ : ℝ) (f : E → F) (x : E) :
    (∫ z in ball 0 ρ, f (x + z) ∂τ) = ∫ y in ball x ρ, f y ∂τ := by
  calc
    _ = ∫ z, (ball x ρ).indicator f (x + z) ∂τ := by
      rw [← integral_indicator isOpen_ball.measurableSet]
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : ‖z‖ < ρ <;> simp [indicator_apply, mem_ball, dist_eq_norm, hz]
    _ = ∫ y, (ball x ρ).indicator f y ∂τ := integral_add_left_eq_self (μ := τ) _ x
    _ = _ := integral_indicator isOpen_ball.measurableSet

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem ballAverage_eq_translatedIntegral (τ : Measure E) [τ.IsAddHaarMeasure]
    (ρ : ℝ) (hρ : 0 < ρ) (f : E → F) (x : E) :
    ballAverage τ ρ hρ f x = (τ (ball (0 : E) ρ)).toReal⁻¹ • ∫ y in ball x ρ, f y ∂τ := by
  rw [ballAverage_eq_setIntegral, setIntegral_ball_translate]

end NCBall
