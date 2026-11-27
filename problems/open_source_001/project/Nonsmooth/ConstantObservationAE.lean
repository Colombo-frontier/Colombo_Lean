import Nonsmooth.GaussianSlabSelection

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem ae_constant_observation_posterior {α β : Type}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    (μ : Measure β) [IsProbabilityMeasure μ] (X : β → α) (hX : Measurable X)
    (c : α) (hc : ∀ᵐ z ∂μ, X z = c) :
    ∀ᵐ y ∂μ.map X, condDistrib id X μ y = μ := by
  have hm : μ.map X = μ.map (fun _ : β => c) := Measure.map_congr hc
  have hj : μ.map (fun z : β => (X z, z)) = μ.map (fun z : β => (c, z)) :=
    Measure.map_congr (hc.mono (fun _ h => Prod.ext h rfl))
  have hjoint : μ.map (fun z : β => (X z, z)) = (μ.map X) ⊗ₘ Kernel.const α μ := by
    rw [hj, hm]
    simp only [Measure.map_const, measure_univ, one_smul]
    ext S hS
    rw [Measure.map_apply measurable_prodMk_left hS, Measure.dirac_compProd_apply hS, Kernel.const_apply]
  have he := (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX measurable_id hjoint).symm
  exact he.mono (fun _ h => h.symm)

/-- A positive-probability event whose truth is almost surely already determined
does not change the prior. -/
theorem cond_eq_self_of_ae_event_decision {β : Type} [MeasurableSpace β]
    (μ : Measure β) [IsProbabilityMeasure μ] (A : Set β) (hA : MeasurableSet A)
    (p : Prop) (hdecision : ∀ᵐ z ∂μ, z ∈ A ↔ p) (hpos : μ A ≠ 0) : μ[|A] = μ := by
  have hp : p := by
    by_contra hp
    have hs : A =ᵐ[μ] (∅ : Set β) := hdecision.mono (fun z hz => by
      apply propext
      change z ∈ A ↔ False
      simp only [hz, hp])
    apply hpos
    rw [measure_congr hs, measure_empty]
  exact cond_eq_self_of_ae_mem μ hA (hdecision.mono (fun _ hz => hz.mpr hp))

theorem constant_real_observation_condition {β : Type} [MeasurableSpace β]
    (μ : Measure β) [IsProbabilityMeasure μ] (X : β → ℝ) (hX : Measurable X)
    (c : ℝ) (hc : ∀ᵐ z ∂μ, X z = c) (D : Set ℝ) (hD : MeasurableSet D)
    (hpos : μ (X ⁻¹' D) ≠ 0) : μ[|X ⁻¹' D] = μ := by
  apply cond_eq_self_of_ae_event_decision μ (X ⁻¹' D) (hX hD) (c ∈ D) _ hpos
  filter_upwards [hc] with z hz
  change X z ∈ D ↔ c ∈ D
  rw [hz]

end
end Nonsmooth
