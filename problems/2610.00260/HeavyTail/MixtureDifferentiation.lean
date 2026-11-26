import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-! Differentiation under the integral within a constrained parameter set.
The pointwise derivative and an integrable first-difference envelope imply the
derivative of the integral; the integrated derivative is not a hypothesis. -/

noncomputable section
open MeasureTheory Filter Metric
open scoped Topology

namespace HeavyTail

theorem hasFDerivWithinAt_integral_of_dominated_difference
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {x₀ : E} {F : E → Ω → ℝ} {F' : Ω → E →L[ℝ] ℝ} {B : Ω → ℝ}
    (hx₀ : x₀ ∈ S) (hF : ∀ x ∈ S, Integrable (F x) μ)
    (hF' : Integrable F' μ) (hB : Integrable B μ) (hBpos : ∀ ω, 0 ≤ B ω)
    (hlip : ∀ᵐ ω ∂μ, ∀ x ∈ S, ‖F x ω - F x₀ ω‖ ≤ B ω * ‖x - x₀‖)
    (hdiff : ∀ᵐ ω ∂μ, HasFDerivWithinAt (fun x => F x ω) (F' ω) S x₀) :
    HasFDerivWithinAt (fun x => ∫ ω, F x ω ∂μ) (∫ ω, F' ω ∂μ) S x₀ := by
  let R : E → Ω → ℝ := fun x ω =>
    ‖x - x₀‖⁻¹ • (F x ω - F x₀ ω - F' ω (x - x₀))
  have hres : Tendsto (fun x => ∫ ω, R x ω ∂μ) (𝓝[S] x₀) (𝓝 (∫ _ : Ω, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun ω => B ω + ‖F' ω‖)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact (((hF x hx).aestronglyMeasurable.sub (hF x₀ hx₀).aestronglyMeasurable).sub
        (hF'.aestronglyMeasurable.apply_continuousLinearMap _)).const_smul (‖x - x₀‖⁻¹ : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      filter_upwards [hlip] with ω hω
      dsimp [R]
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      calc
        _ ≤ ‖x - x₀‖⁻¹ * (‖F x ω - F x₀ ω‖ + ‖F' ω (x - x₀)‖) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
          simpa only [Real.norm_eq_abs] using
            (norm_sub_le (F x ω - F x₀ ω) (F' ω (x - x₀)))
        _ ≤ ‖x - x₀‖⁻¹ * (B ω * ‖x - x₀‖ + ‖F' ω‖ * ‖x - x₀‖) := by
          exact mul_le_mul_of_nonneg_left (add_le_add (hω x hx) ((F' ω).le_opNorm _))
            (inv_nonneg.mpr (norm_nonneg _))
        _ ≤ B ω + ‖F' ω‖ := by
          by_cases hzero : x - x₀ = 0
          · simp only [hzero, norm_zero, inv_zero, mul_zero, add_zero, zero_mul]
            exact add_nonneg (hBpos ω) (norm_nonneg _)
          · have hn : ‖x - x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
            have he : ‖x - x₀‖⁻¹ * (B ω * ‖x - x₀‖ + ‖F' ω‖ * ‖x - x₀‖) =
                B ω + ‖F' ω‖ := by
              calc
                _ = (B ω + ‖F' ω‖) * (‖x - x₀‖⁻¹ * ‖x - x₀‖) := by ring
                _ = _ := by rw [inv_mul_cancel₀ hn, mul_one]
            exact he.le
    · exact hB.add hF'.norm
    · filter_upwards [hdiff] with ω hω
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [R, smul_eq_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
          (hasFDerivWithinAt_iff_tendsto.mp hω)
  have heq : ∀ᶠ x in 𝓝[S] x₀,
      ‖x - x₀‖⁻¹ * ‖(∫ ω, F x ω ∂μ) - (∫ ω, F x₀ ω ∂μ) -
        (∫ ω, F' ω ∂μ) (x - x₀)‖ = ‖∫ ω, R x ω ∂μ‖ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hsubint : Integrable (fun ω => F x ω - F x₀ ω) μ := (hF x hx).sub (hF x₀ hx₀)
    dsimp [R]
    rw [integral_const_mul, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      integral_sub hsubint (hF'.apply_continuousLinearMap _),
      integral_sub (hF x hx) (hF x₀ hx₀), ContinuousLinearMap.integral_apply hF']
  rw [hasFDerivWithinAt_iff_tendsto]
  have hrnorm := hres.norm
  simp only [integral_zero, norm_zero] at hrnorm
  exact (tendsto_congr' heq).mpr hrnorm

end HeavyTail
