import Nonsmooth.RankBoundLimit
import Nonsmooth.RegularVectorEnergy

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- A target posterior inherits the uniform rank estimate from regular row
approximations once posterior means and marginal CDFs converge. -/
theorem regular_projection_rank_of_approximation (μ : Measure E) [IsProbabilityMeasure μ]
    (Q : ℕ → Measure E) [∀ n, IsProbabilityMeasure (Q n)]
    {u : E} (hu : ‖u‖ = 1) (hd : 2 ≤ Module.finrank ℝ E)
    (H : ∀ n (v : E), ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 → RegularProjectionImage (Q n) u v)
    (hatom : ∀ y : ℝ, μ {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (hAC : ∀ n, μ.map (fun z : E => ⟪z, u⟫_ℝ) ≪ (Q n).map (fun z : E => ⟪z, u⟫_ℝ))
    (hm : ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      Tendsto (fun n => projectionPosteriorShift (Q n) u y) atTop (𝓝 (projectionPosteriorShift μ u y)))
    (hcdf : ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      Tendsto (fun n => cdf ((Q n).map (fun z : E => ⟪z, u⟫_ℝ)) y) atTop
        (𝓝 (cdf (μ.map (fun z : E => ⟪z, u⟫_ℝ)) y))) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      ‖projectionPosteriorShift μ u y‖ ^ 2 ≤
        72 * (1 + rankQuantileLog (cdf (μ.map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
  have hX : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  letI : IsProbabilityMeasure (μ.map (fun z : E => ⟪z, u⟫_ℝ)) := Measure.isProbabilityMeasure_map hX.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure ((Q n).map (fun z : E => ⟪z, u⟫_ℝ)) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  apply ae_rank_bound_of_approximation _ _ _ hAC
    (fun n => projectionPosteriorShift (Q n) u) (projectionPosteriorShift μ u) 72 _ hm hcdf
  · intro y
    rw [Measure.map_apply hX (measurableSet_singleton y)]
    exact hatom y
  · intro n
    exact regular_vector_projection_no_spike (Q n)
      ((regular_vector_memLp_two (Q n) hu hd (H n)).integrable (by norm_num)) hu hd (H n)

end
end Nonsmooth
