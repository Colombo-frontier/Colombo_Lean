import Nonsmooth.OrthogonalPlaneBounds
import Nonsmooth.RegularProjectionNoSpike
import Nonsmooth.RegularSliceSelection

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Explicit analytic data for a regular two-coordinate image. This structure
contains density identification and local regularity, with no posterior bound. -/
structure RegularProjectionImage (μ : Measure E) (u v : E) where
  potential : ℝ → ℝ → ℝ
  forward : RegularStrongSliceFamily potential
  backward : RegularStrongSliceFamily (fun t x => potential x t)
  moments : RegularSliceMomentContinuity potential forward
  law : μ.map (fun z : E => (⟪z, u⟫_ℝ, ⟪v, z⟫_ℝ)) = potentialJointLaw potential

theorem regular_projection_image_marginal (μ : Measure E) (u v : E)
    (H : RegularProjectionImage μ u v) :
    μ.map (fun z : E => ⟪z, u⟫_ℝ) = realDensityLaw (potentialPartition H.potential) := by
  have hX : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have hY : Measurable (fun z : E => ⟪v, z⟫_ℝ) := (continuous_const.inner continuous_id).measurable
  rw [← potentialJointLaw_marginal H.potential H.forward.measurable
    (regularFamily_slice_integrable H.forward), ← H.law,
    Measure.map_map measurable_fst (hX.prodMk hY)]
  rfl

theorem regular_projection_image_atomless (μ : Measure E) (u v : E)
    (H : RegularProjectionImage μ u v) (y : ℝ) : μ {z : E | ⟪z, u⟫_ℝ = y} = 0 := by
  have hX : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have h := realDensityLaw_atomless (potentialPartition H.potential) y
  rw [← regular_projection_image_marginal μ u v H, Measure.map_apply hX (measurableSet_singleton y)] at h
  exact h

theorem regular_projection_image_bound (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (u v : E) (H : RegularProjectionImage μ u v) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      ⟪u, projectionPosteriorShift μ u y⟫_ℝ ^ 2 + ⟪v, projectionPosteriorShift μ u y⟫_ℝ ^ 2 ≤
        72 * (1 + rankQuantileLog (cdf (μ.map (fun z : E => ⟪z, u⟫_ℝ)) y)) :=
  regular_projection_no_spike μ hi u v H.forward H.backward H.moments H.law

/-- The actual vector posterior shift satisfies a dimension-free rank bound
when all transverse two-coordinate images have the stated regular densities. -/
theorem regular_vector_projection_no_spike (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) {u : E} (hu : ‖u‖ = 1)
    (hd : 2 ≤ Module.finrank ℝ E)
    (H : ∀ v : E, ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 → RegularProjectionImage μ u v) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      ‖projectionPosteriorShift μ u y‖ ^ 2 ≤
        72 * (1 + rankQuantileLog (cdf (μ.map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
  obtain ⟨w, hw, huw⟩ := exists_unit_orthogonal_direction hu hd
  have hbase := (regular_projection_image_bound μ hi u w (H w hw huw)).mono
    (fun y hy => (le_add_of_nonneg_right (sq_nonneg _)).trans hy)
  apply ae_norm_sq_bound_of_planes _ _ _ hu hbase
  exact fun v hv huv => regular_projection_image_bound μ hi u v (H v hv huv)

end
end Nonsmooth
