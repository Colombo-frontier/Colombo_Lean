import Nonsmooth.SoftProjectionLimit
import Nonsmooth.SoftWeightCDF
import Nonsmooth.ProjectionRankApproximation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The hard event-conditioned posterior inherits the rank bound from regular
soft-weight approximations. Posterior, CDF and null-set convergence conditions
are all established internally. -/
theorem soft_projection_rank_bound (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) {u : E} (hu : ‖u‖ = 1)
    (hd : 2 ≤ Module.finrank ℝ E) (hatom : ∀ y : ℝ, μ {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (w : ℕ → E → ℝ) (hw : ∀ n, Measurable (w n))
    (hb : ∀ n z, 0 ≤ w n z ∧ w n z ≤ 1) (hp : ∀ n, ∀ᵐ z ∂μ, 0 < w n z)
    (A : Set E) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun n => w n z) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) z)))
    (H : ∀ n (v : E), ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 → RegularProjectionImage (weightedDensityLaw μ (w n)) u v) :
    letI : IsProbabilityMeasure μ[|A] := cond_isProbabilityMeasure hpos
    ∀ᵐ y ∂μ[|A].map (fun z : E => ⟪z, u⟫_ℝ),
      ‖projectionPosteriorShift μ[|A] u y‖ ^ 2 ≤
        72 * (1 + rankQuantileLog (cdf (μ[|A].map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
  letI : IsProbabilityMeasure μ[|A] := cond_isProbabilityMeasure hpos
  letI (n : ℕ) : IsProbabilityMeasure (weightedDensityLaw μ (w n)) :=
    weightedDensityLaw_probability_of_positive μ (w n) (hw n) (hb n) (hp n)
  have hX : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  apply regular_projection_rank_of_approximation μ[|A] (fun n => weightedDensityLaw μ (w n)) hu hd H
  · exact fun y => cond_absolutelyContinuous (hatom y)
  · intro n
    apply absolutelyContinuous_map_measurable _ _ _ _ hX
    exact cond_absolutelyContinuous.trans (absolutelyContinuous_weightedDensityLaw μ (w n) (hw n)
      (unit_weight_integrable μ (w n) (hw n) (hb n)) (fun z => (hb n z).1) (hp n))
  · exact soft_projection_shift_tendsto μ hi u w hw hb hp A hA hpos hlim
  · exact Eventually.of_forall (fun y => soft_weighted_cdf_tendsto μ w hw hb hp A hA hpos hlim _ hX y)

end
end Nonsmooth
