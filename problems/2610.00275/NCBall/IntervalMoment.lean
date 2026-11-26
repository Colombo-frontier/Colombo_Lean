import NCBall.LipschitzInterval
import NCBall.NoiseMoments

/-! # A scalar interval average cannot increase the second moment -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
namespace NCBall

theorem ballLaw_real_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ) (hρ : 0 < ρ) (g : ℝ → F) :
    (∫ t, g t ∂ballLaw volume ρ hρ) = (2 * ρ)⁻¹ • ∫ t in (-ρ)..ρ, g t := by
  simpa only [ballAverage, zero_add, zero_sub] using ballAverage_real_interval ρ hρ g 0

theorem interval_average_square_le {a : ℝ → ℝ} (ha : Measurable a) {B : ℝ}
    (hbound : ∀ t, ‖a t‖ ≤ B) {ρ q : ℝ} (hρ : 0 ≤ ρ)
    (hmean : (∫ t in (-ρ)..ρ, a t) = (2 * ρ) * q) :
    (2 * ρ) * q ^ 2 ≤ ∫ t in (-ρ)..ρ, (a t) ^ 2 := by
  rcases hρ.eq_or_lt with rfl | hρ
  · simp
  · have hp : 0 < 2 * ρ := by positivity
    have hLp : MemLp a 2 (ballLaw volume ρ hρ) :=
      MemLp.of_bound ha.aestronglyMeasurable B (Filter.Eventually.of_forall hbound)
    have hv := variance_nonneg a (ballLaw volume ρ hρ)
    rw [variance_def' hLp] at hv
    simp only [Pi.pow_apply] at hv
    rw [ballLaw_real_integral ρ hρ a,
      ballLaw_real_integral ρ hρ (fun t => (a t) ^ 2), smul_eq_mul, smul_eq_mul, hmean] at hv
    have he : (2 * ρ)⁻¹ * ((2 * ρ) * q) = q := by field_simp
    rw [he] at hv
    have hq : q ^ 2 ≤ (∫ t in (-ρ)..ρ, (a t) ^ 2) / (2 * ρ) := by
      simpa only [div_eq_mul_inv, mul_comm] using (sub_nonneg.mp hv)
    simpa only [mul_comm] using (le_div_iff₀ hp).mp hq

end NCBall
