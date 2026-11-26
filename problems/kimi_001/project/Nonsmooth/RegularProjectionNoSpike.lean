import Nonsmooth.RegularJointPosterior
import Nonsmooth.ProjectionPosteriorDirection
import Nonsmooth.ObservationEventStability

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem projectionPosteriorShift_observed (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (u : E) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      ⟪u, projectionPosteriorShift μ u y⟫_ℝ = y - ∫ z : E, ⟪z, u⟫_ℝ ∂μ := by
  let X : E → ℝ := fun z => ⟪z, u⟫_ℝ
  have hX : Measurable X := (continuous_id.inner continuous_const).measurable
  have hpair : Integrable (fun p : ℝ × E => p.2) (μ.map (fun z => (X z, z))) :=
    hi.comp_snd_map_prodMk X
  have hki := hpair.condDistrib_ae_map (Y := id) aemeasurable_id
  filter_upwards [hki, condDistrib_real_fiber μ X hX] with y hy hf
  change Integrable (fun z : E => z) (condDistrib id X μ y) at hy
  change ⟪u, ∫ z : E, (z - ∫ a : E, a ∂μ) ∂condDistrib id X μ y⟫_ℝ = _
  rw [integral_sub hy (integrable_const _), integral_const, measureReal_univ_eq_one, one_smul,
    inner_sub_right, ← integral_inner hy, ← integral_inner hi]
  have he : (∫ z : E, ⟪u, z⟫_ℝ ∂condDistrib id X μ y) = y := by
    calc
      _ = ∫ _ : E, y ∂condDistrib id X μ y := by
        apply integral_congr_ae
        filter_upwards [hf] with z hz
        exact (real_inner_comm _ _).trans hz
      _ = y := by simp
  rw [he]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => real_inner_comm _ _)

/-- A regular two-coordinate image controls the corresponding two components
of the actual vector posterior shift. -/
theorem regular_projection_no_spike (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (u v : E)
    {V : ℝ → ℝ → ℝ} (H : RegularStrongSliceFamily V)
    (G : RegularStrongSliceFamily (fun t x => V x t)) (C : RegularSliceMomentContinuity V H)
    (hlaw : μ.map (fun z : E => (⟪z, u⟫_ℝ, ⟪v, z⟫_ℝ)) = potentialJointLaw V) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      ⟪u, projectionPosteriorShift μ u y⟫_ℝ ^ 2 + ⟪v, projectionPosteriorShift μ u y⟫_ℝ ^ 2 ≤
        72 * (1 + rankQuantileLog (cdf (μ.map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
  have hX : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have hY : Measurable (fun z : E => ⟪v, z⟫_ℝ) := (continuous_const.inner continuous_id).measurable
  filter_upwards [regular_joint_image_no_spike μ _ _ hX hY H G C hlaw,
    projectionPosteriorShift_observed μ hi u, projectionPosteriorShift_inner μ hi u v] with y hy hu hv
  rw [hu, hv]
  exact hy

end
end Nonsmooth
