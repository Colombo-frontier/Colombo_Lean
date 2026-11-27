import Nonsmooth.GaussianSliceCovariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem compProd_map_hidden (ν : Measure α) [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] (f : β → γ) (hf : Measurable f) :
    (ν ⊗ₘ κ).map (fun p : α × β => (p.1, f p.2)) = ν ⊗ₘ κ.map f := by
  have hT : Measurable (fun p : α × β => (p.1, f p.2)) :=
    measurable_fst.prodMk (hf.comp measurable_snd)
  letI : IsMarkovKernel (κ.map f) := Kernel.IsMarkovKernel.map κ hf
  ext S hS
  rw [Measure.map_apply hT hS, Measure.compProd_apply (hT hS), Measure.compProd_apply hS]
  apply lintegral_congr
  intro x
  rw [Kernel.map_apply' κ hf x (measurable_prodMk_left hS)]
  rfl

theorem variance_map_measurable (μ : Measure β) (f : β → γ) (hf : Measurable f)
    (g : γ → ℝ) (hg : Measurable g) :
    variance g (μ.map f) = variance (g ∘ f) μ := by
  rw [variance_eq_integral hg.aemeasurable,
    integral_map_of_stronglyMeasurable hf hg.stronglyMeasurable]
  have hc : StronglyMeasurable (fun z : γ => (g z - ∫ y : β, g (f y) ∂μ) ^ 2) :=
    (hg.stronglyMeasurable.sub stronglyMeasurable_const).pow 2
  rw [integral_map_of_stronglyMeasurable hf hc, variance_eq_integral (hg.comp hf).aemeasurable]
  rfl

variable [StandardBorelSpace β] [Nonempty β]

theorem condDistrib_image_disintegration (μ : Measure β) [IsProbabilityMeasure μ]
    (X : β → α) (hX : Measurable X) (f : β → γ) (hf : Measurable f) :
    μ.map (fun z => (X z, f z)) = (μ.map X) ⊗ₘ (condDistrib id X μ).map f := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hpair : Measurable (fun z : β => (X z, z)) := hX.prodMk measurable_id
  have hT : Measurable (fun p : α × β => (p.1, f p.2)) :=
    measurable_fst.prodMk (hf.comp measurable_snd)
  have h := congrArg (fun ν : Measure (α × β) => ν.map (fun p => (p.1, f p.2)))
    (compProd_map_condDistrib (X := X) (μ := μ) (mβ := inferInstance) aemeasurable_id)
  dsimp only [id_eq] at h
  rw [compProd_map_hidden _ _ f hf, Measure.map_map hT hpair] at h
  exact h.symm

variable [StandardBorelSpace γ] [Nonempty γ]

/-- Pushing forward the hidden variable and its prior commutes with the actual
regular conditional distribution, with the observation pulled back along that map. -/
theorem condDistrib_map_prior (μ : Measure β) [IsProbabilityMeasure μ]
    (f : β → γ) (hf : Measurable f) (X : γ → α) (hX : Measurable X) :
    ∀ᵐ x ∂(μ.map f).map X,
      condDistrib id X (μ.map f) x = (condDistrib id (X ∘ f) μ x).map f := by
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  let κ := (condDistrib id (X ∘ f) μ).map f
  letI : IsMarkovKernel κ := Kernel.IsMarkovKernel.map _ hf
  have hpair : Measurable (fun z : γ => (X z, z)) := hX.prodMk measurable_id
  have hjoint : (μ.map f).map (fun z => (X z, z)) = ((μ.map f).map X) ⊗ₘ κ := by
    rw [Measure.map_map hpair hf, Measure.map_map hX hf]
    exact condDistrib_image_disintegration μ (X ∘ f) (hX.comp hf) f hf
  have he := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX measurable_id (κ := κ) hjoint
  filter_upwards [he] with x hx
  rw [hx]
  exact Kernel.map_apply _ hf _

end
end Nonsmooth
