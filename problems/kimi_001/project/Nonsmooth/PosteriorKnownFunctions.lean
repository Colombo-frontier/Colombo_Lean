import Nonsmooth.PosteriorRowMoments

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem measurable_comap_fiber_equal {α β γ : Type} [MeasurableSpace α]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (f : β → α) (g : β → γ) (hg : Measurable[MeasurableSpace.comap f inferInstance] g)
    {a b : β} (hab : f b = f a) : g b = g a := by
  obtain ⟨S, _, hS⟩ := hg (measurableSet_singleton (g a))
  have ha : f a ∈ S := by
    change a ∈ f ⁻¹' S
    rw [hS]
    exact rfl
  have hb : f b ∈ S := hab ▸ ha
  have he : b ∈ g ⁻¹' {g a} := by
    rw [← hS]
    exact hb
  exact he

/-- Every almost-sure hidden-state property is inherited by its regular conditional law. -/
theorem condDistrib_ae_inherits {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace β] [Nonempty β]
    (Q : Measure β) [IsProbabilityMeasure Q] (F : β → α) (hF : Measurable F)
    {P : β → Prop} (h : ∀ᵐ b ∂Q, P b) :
    ∀ᵐ x ∂Q.map F, ∀ᵐ b ∂condDistrib id F Q x, P b := by
  have hp : Measurable (fun b : β => (F b, b)) := hF.prodMk measurable_id
  have hs : ((Q.map F) ⊗ₘ condDistrib id F Q).map Prod.snd = Q := by
    rw [compProd_map_condDistrib aemeasurable_id]
    dsimp only [id_eq]
    rw [Measure.map_map measurable_snd hp]
    exact Measure.map_id
  rw [← hs] at h
  exact Measure.ae_ae_of_ae_compProd (ae_of_ae_map measurable_snd.aemeasurable h)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {k : ℕ} [Nonempty (Fin k)]
  {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

/-- A history-measurable function is almost surely constant under the posterior at that history. -/
theorem supportPosteriorKernel_known_function
    (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ)
    (X : (Fin k → E) → E) (hX : AEStronglyMeasurable[supportTranscriptInformation p ω n] X Q) :
    ∀ᵐ a ∂Q, ∀ᵐ b ∂supportPosteriorKernel Q p ω n (supportAugmentedTranscript p a ω n), X b = X a := by
  let F : (Fin k → E) → SupportHistory E k n := fun a => supportAugmentedTranscript p a ω n
  have hF : Measurable F := (supportAugmentedTranscript_measurable p hp n).comp
    (measurable_id.prodMk (measurable_const (a := ω)))
  have hm : Measurable[MeasurableSpace.comap F inferInstance] (hX.mk X) :=
    hX.stronglyMeasurable_mk.measurable
  have hpost := ae_of_ae_map hF.aemeasurable (condDistrib_ae_inherits Q F hF hX.ae_eq_mk)
  have hfiber := ae_of_ae_map hF.aemeasurable (supportPosteriorKernel_fiber Q p hp ω n)
  filter_upwards [hX.ae_eq_mk, hpost, hfiber] with a ha hb hf
  filter_upwards [hb, hf] with b hb hba
  exact hb.trans ((measurable_comap_fiber_equal F (hX.mk X) hm hba).trans ha.symm)

end
end Nonsmooth
