import Nonsmooth.ObservationEventStability

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem probability_eq_dirac_of_ae_eq {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (x : α) (hx : ∀ᵐ z ∂μ, z = x) :
    μ = Measure.dirac x := by
  have hm : μ.map (fun z => z) = μ.map (fun _ => x) := Measure.map_congr hx
  change μ.map id = μ.map (fun _ => x) at hm
  simpa only [Measure.map_id, Measure.map_const, measure_univ, one_smul] using hm

theorem recoverable_real_observation_posterior {β : Type}
    [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    (μ : Measure β) [IsProbabilityMeasure μ] (X : β → ℝ) (hX : Measurable X)
    (g : ℝ → β) (hg : ∀ z, g (X z) = z) :
    ∀ᵐ y ∂μ.map X, condDistrib id X μ y = Measure.dirac (g y) := by
  filter_upwards [condDistrib_real_fiber μ X hX] with y hy
  apply probability_eq_dirac_of_ae_eq
  filter_upwards [hy] with z hz
  rw [← hg z, hz]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- A unit observation that spans the remaining space determines the whole
row. This is the final one-dimensional case of the winner update. -/
theorem spanning_unit_observation_posterior (μ : Measure E) [IsProbabilityMeasure μ]
    {u : E} (hu : ‖u‖ = 1) (hspan : (ℝ ∙ u : Submodule ℝ E) = ⊤) :
    ∀ᵐ y ∂μ.map (fun z : E => ⟪z, u⟫_ℝ),
      condDistrib id (fun z : E => ⟪z, u⟫_ℝ) μ y = Measure.dirac (y • u) := by
  apply recoverable_real_observation_posterior μ _ (by fun_prop) (fun y => y • u)
  intro z
  have hp := unit_orthogonalProjection_formula hu z
  have hz : z ∈ (ℝ ∙ u : Submodule ℝ E) := by rw [hspan]; trivial
  exact hp.symm.trans (((ℝ ∙ u : Submodule ℝ E).starProjection_eq_self_iff).mpr hz)

end
end Nonsmooth
