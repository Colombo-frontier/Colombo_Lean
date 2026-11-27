import Nonsmooth.ConditionalEventKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

theorem event_restricted_joint_disintegration (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : μ.map (fun z => (X z, z)) = (μ.map X) ⊗ₘ κ)
    (A : Set β) (hA : MeasurableSet A) :
    (μ.restrict A).map (fun z => (X z, z)) =
      ((μ.map X).withDensity (fun x => κ x A)) ⊗ₘ conditionalEventKernel κ A hA := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hpair : Measurable (fun z : β => (X z, z)) := hX.prodMk measurable_id
  have hr : (μ.restrict A).map (fun z => (X z, z)) =
      (μ.map (fun z => (X z, z))).restrict (Prod.snd ⁻¹' A) := by
    rw [Measure.restrict_map hpair (measurable_snd hA)]
    rfl
  rw [hr, hκ, conditionalEventKernel_restrict_disintegration]

theorem event_restricted_observation_density (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : μ.map (fun z => (X z, z)) = (μ.map X) ⊗ₘ κ)
    (A : Set β) (hA : MeasurableSet A) :
    (μ.restrict A).map X = (μ.map X).withDensity (fun x => κ x A) := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  letI := kernel_event_density_finite (μ.map X) κ A
  have hpair : Measurable (fun z : β => (X z, z)) := hX.prodMk measurable_id
  have he := congrArg (fun ν : Measure (α × β) => ν.map Prod.fst)
    (event_restricted_joint_disintegration μ X hX κ hκ A hA)
  try dsimp only at he
  rw [Measure.map_map measurable_fst hpair,
    ← Measure.fst, Measure.fst_compProd] at he
  exact he

theorem event_conditioned_joint_disintegration (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : μ.map (fun z => (X z, z)) = (μ.map X) ⊗ₘ κ)
    (A : Set β) (hA : MeasurableSet A) :
    μ[|A].map (fun z => (X z, z)) = (μ[|A].map X) ⊗ₘ conditionalEventKernel κ A hA := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  letI := kernel_event_density_finite (μ.map X) κ A
  simp only [ProbabilityTheory.cond, Measure.map_smul]
  rw [event_restricted_joint_disintegration μ X hX κ hκ A hA,
    event_restricted_observation_density μ X hX κ hκ A hA, Measure.compProd_smul_left]

theorem event_conditioned_slice_positive (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : μ.map (fun z => (X z, z)) = (μ.map X) ⊗ₘ κ)
    (A : Set β) (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ[|A].map X, κ x A ≠ 0 := by
  have hpos : ∀ᵐ x ∂(μ.map X).withDensity (fun x => κ x A), κ x A ≠ 0 := by
    rw [ae_withDensity_iff (κ.measurable_coe hA)]
    exact Eventually.of_forall (fun _ hx => hx)
  rw [ProbabilityTheory.cond, Measure.map_smul,
    event_restricted_observation_density μ X hX κ hκ A hA]
  exact Measure.ae_smul_measure hpos _

variable [StandardBorelSpace β] [Nonempty β]

/-- Conditioning the prior on an event conditions almost every original posterior
on that event. This remains valid for continuous observations with null fibers. -/
theorem event_conditioned_posterior (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (κ : Kernel α β) [IsMarkovKernel κ]
    (hκ : μ.map (fun z => (X z, z)) = (μ.map X) ⊗ₘ κ)
    (A : Set β) (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ[|A].map X,
      condDistrib id X μ[|A] x = (κ x)[|A] ∧ κ x A ≠ 0 := by
  have he := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX measurable_id
    (κ := conditionalEventKernel κ A hA)
    (event_conditioned_joint_disintegration μ X hX κ hκ A hA)
  filter_upwards [he, event_conditioned_slice_positive μ X hX κ hκ A hA] with x hx hp
  exact ⟨hx.trans (conditionalEventKernel_apply κ A hA x hp), hp⟩

end
end Nonsmooth
