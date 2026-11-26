import Nonsmooth.ConditionalImage
import Nonsmooth.ConditionalReencoding

open MeasureTheory ProbabilityTheory Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
  [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty α] [Nonempty β]

/-- An affine change of the scalar observation and a measurable change of the
hidden state commute with the actual conditional distribution. -/
theorem affine_observation_posterior (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (r : α → ℝ) (hr : Measurable r)
    (X : β → ℝ) (hX : Measurable X) {c : ℝ} (hc : c ≠ 0) (o : ℝ)
    (hXf : ∀ z, X (f z) = o + c * r z) :
    ∀ᵐ y ∂(μ.map f).map X,
      condDistrib id X (μ.map f) y =
        (condDistrib id r μ ((y - o) / c)).map f := by
  let e : ℝ → ℝ := fun t => o + c * t
  let g : ℝ → ℝ := fun y => (y - o) / c
  have he : Measurable e := by fun_prop
  have hg : Measurable g := by fun_prop
  have hZ : Measurable (X ∘ f) := hX.comp hf
  have hZX (z : α) : (X ∘ f) z = e (r z) := hXf z
  have hXZ (z : α) : g ((X ∘ f) z) = r z := by
    rw [hZX]
    dsimp only [g, e]
    field_simp
    ring
  have hp := condDistrib_reencoding μ r hr id measurable_id (X ∘ f) hZ e he g hg hZX hXZ
  have hm := condDistrib_map_prior μ f hf X hX
  rw [Measure.map_map hX hf] at hm ⊢
  filter_upwards [hp, hm] with y hy hm
  rw [hm, ← hy]

theorem affine_observation_law_inverse (μ : Measure α)
    (f : α → β) (hf : Measurable f) (r : α → ℝ) (hr : Measurable r)
    (X : β → ℝ) (hX : Measurable X) {c : ℝ} (hc : c ≠ 0) (o : ℝ)
    (hXf : ∀ z, X (f z) = o + c * r z) :
    ((μ.map f).map X).map (fun y => (y - o) / c) = μ.map r := by
  have hg : Measurable (fun y : ℝ => (y - o) / c) := by fun_prop
  rw [Measure.map_map hX hf, Measure.map_map hg (hX.comp hf)]
  congr 1
  funext z
  simp only [Function.comp_def, hXf]
  field_simp
  ring

theorem affine_observation_posterior_property (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (r : α → ℝ) (hr : Measurable r)
    (X : β → ℝ) (hX : Measurable X) {c : ℝ} (hc : c ≠ 0) (o : ℝ)
    (hXf : ∀ z, X (f z) = o + c * r z)
    (P : ℝ → Measure β → Prop)
    (hP : ∀ᵐ t ∂μ.map r, P t ((condDistrib id r μ t).map f)) :
    ∀ᵐ y ∂(μ.map f).map X, P ((y - o) / c) (condDistrib id X (μ.map f) y) := by
  have hg : Measurable (fun y : ℝ => (y - o) / c) := by fun_prop
  rw [← affine_observation_law_inverse μ f hf r hr X hX hc o hXf] at hP
  have hpull := ae_of_ae_map hg.aemeasurable hP
  filter_upwards [hpull, affine_observation_posterior μ f hf r hr X hX hc o hXf] with y hy he
  rw [he]
  exact hy

end
end Nonsmooth
