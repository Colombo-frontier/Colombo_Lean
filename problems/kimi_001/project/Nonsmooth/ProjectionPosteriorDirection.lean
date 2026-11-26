import Nonsmooth.SupportWinnerRank
import Nonsmooth.ConditionalJointImage

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Directional evaluation of the actual vector posterior mean agrees with
the centered scalar conditional mean for the same observation. -/
theorem projectionPosteriorShift_inner (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z : E => z) μ) (u v : E) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      ⟪v, projectionPosteriorShift μ u y⟫_ℝ =
        (∫ w : ℝ, w ∂condDistrib (fun z : E => ⟪v, z⟫_ℝ) (fun z : E => ⟪z, u⟫_ℝ) μ y) -
          ∫ z : E, ⟪v, z⟫_ℝ ∂μ := by
  let X : E → ℝ := fun z => ⟪z, u⟫_ℝ
  let Y : E → ℝ := fun z => ⟪v, z⟫_ℝ
  have hX : Measurable X := (continuous_id.inner continuous_const).measurable
  have hY : Measurable Y := (continuous_const.inner continuous_id).measurable
  have hpair : Integrable (fun p : ℝ × E => p.2) (μ.map (fun z => (X z, z))) :=
    hi.comp_snd_map_prodMk X
  have hki := hpair.condDistrib_ae_map (Y := id) aemeasurable_id
  filter_upwards [hki, condDistrib_hidden_image_ae μ X hX Y hY] with y hy hm
  change Integrable (fun z : E => z) (condDistrib id X μ y) at hy
  change ⟪v, ∫ z : E, (z - ∫ a : E, a ∂μ) ∂condDistrib id X μ y⟫_ℝ =
    (∫ w : ℝ, w ∂condDistrib Y X μ y) - ∫ z : E, Y z ∂μ
  rw [integral_sub hy (integrable_const _), integral_const, measureReal_univ_eq_one, one_smul,
    inner_sub_right, hm]
  have hmap := integral_map_of_stronglyMeasurable (μ := condDistrib id X μ y) hY
    (stronglyMeasurable_id : StronglyMeasurable (fun w : ℝ => w))
  simp only [id_eq] at hmap
  rw [hmap, integral_inner hy, integral_inner hi]

end
end Nonsmooth
