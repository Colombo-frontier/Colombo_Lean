import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! Retaining all information by a measurable embedding preserves finite KL. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory InformationTheory

theorem llr_map_embedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {f : α → β} (hf : MeasurableEmbedding f) (hPQ : P ≪ Q) :
    (fun x => llr (P.map f) (Q.map f) (f x)) =ᵐ[P] llr P Q := by
  filter_upwards [hPQ.ae_eq (hf.rnDeriv_map P Q)] with x hx
  simp only [llr, hx]

theorem klDiv_map_embedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {f : α → β} (hf : MeasurableEmbedding f) (hPQ : P ≪ Q) (hi : Integrable (llr P Q) P) :
    klDiv (P.map f) (Q.map f) = klDiv P Q := by
  have hi' : Integrable (llr (P.map f) (Q.map f)) (P.map f) := by
    rw [hf.integrable_map_iff]
    exact hi.congr (llr_map_embedding hf hPQ).symm
  rw [klDiv_of_ac_of_integrable (hf.absolutelyContinuous_map hPQ) hi',
    klDiv_of_ac_of_integrable hPQ hi,
    integral_map hf.measurable.aemeasurable (measurable_llr _ _).aestronglyMeasurable,
    integral_congr_ae (llr_map_embedding hf hPQ)]
  simp [measureReal_def, Measure.map_apply hf.measurable MeasurableSet.univ]

end FreshGradientMinimax
