import SecondOrder.FiniteDataProcessing

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

/-- Relative entropy is unchanged by a measurable embedding of the sample space. -/
theorem klDiv_map_embedding {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ ν : Measure A} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : A → B} (hf : MeasurableEmbedding f) (hac : μ ≪ ν) (hi : Integrable (llr μ ν) μ) :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  haveI : IsProbabilityMeasure (μ.map f) := isProbabilityMeasure_map hf.measurable.aemeasurable
  haveI : IsProbabilityMeasure (ν.map f) := isProbabilityMeasure_map hf.measurable.aemeasurable
  have he : (fun x => llr (μ.map f) (ν.map f) (f x)) =ᵐ[μ] llr μ ν := by
    filter_upwards [hac.ae_eq (hf.rnDeriv_map μ ν)] with x hx
    simp only [llr, hx]
  have hi' : Integrable (llr (μ.map f) (ν.map f)) (μ.map f) :=
    hf.integrable_map_iff.mpr (hi.congr he.symm)
  rw [klDiv_of_ac_of_integrable (hf.absolutelyContinuous_map hac) hi',
    klDiv_of_ac_of_integrable hac hi]
  simp only [measureReal_univ_eq_one, add_sub_cancel_right]
  rw [hf.integral_map, integral_congr_ae he]

/-- Finite coefficient randomness may produce responses in any measurable
space with measurable singletons. No finiteness of the ambient response
space is required: first pass to the finite image, then embed it back. -/
theorem klDiv_finite_response {A B : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (p q : PMF A) (hp : ∀ a, p a ≠ 0) (hq : ∀ a, q a ≠ 0) (f : A → B) :
    klDiv (p.toMeasure.map f) (q.toMeasure.map f) ≤ klDiv p.toMeasure q.toMeasure := by
  letI : Fintype (Set.range f) := (Set.finite_range f).fintype
  let g : A → Set.range f := Set.rangeFactorization f
  have hg : Function.Surjective g := Set.surjective_onto_range
  have hgm : Measurable g := measurable_of_countable g
  have he : MeasurableEmbedding (Subtype.val : Set.range f → B) :=
    MeasurableEmbedding.subtype_coe (Set.finite_range f).measurableSet
  have hmap (r : PMF A) : (r.map g).toMeasure.map Subtype.val = r.toMeasure.map f := by
    rw [← PMF.toMeasure_map g r hgm, Measure.map_map he.measurable hgm]
    rfl
  rw [← hmap p, ← hmap q,
    klDiv_map_embedding he (pmf_absolutelyContinuous _ _ (pmf_map_ne_zero q hq hg)) Integrable.of_finite]
  exact klDiv_pmf_map_le p q hp hq hg

end
end SecondOrder
