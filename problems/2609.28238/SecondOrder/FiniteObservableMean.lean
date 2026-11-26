import SecondOrder.ComparisonFarHistory

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

/-- Equality of response laws implies equality of every real test function.
The response space and the test function need not be finite or measurable:
the finite coefficient space supplies a finite common response image. -/
theorem pmfMean_comp_eq_of_map_eq {A B : Type*} [Fintype A]
    (p q : PMF A) (f : A → B) (he : p.map f=q.map f) (F : B → ℝ) :
    pmfMean p (fun a => F (f a))=pmfMean q (fun a => F (f a)) := by
  letI : Fintype (Set.range f) := (Set.finite_range f).fintype
  let g : A → Set.range f := Set.rangeFactorization f
  have hg : p.map g=q.map g := by
    ext b
    have hb := congrArg (fun r : PMF B => r b.val) he
    simp only [PMF.map_apply, tsum_fintype] at hb ⊢
    simpa only [g, Set.rangeFactorization, Subtype.mk.injEq, Subtype.ext_iff] using hb
  have hp := pmfMean_map p g (fun b => F b.val)
  have hq := pmfMean_map q g (fun b => F b.val)
  rw [hg] at hp
  exact hp.symm.trans hq

theorem pmfMean_comp_eq_of_measure_map_eq {A B : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (p q : PMF A) (f : A → B) (he : p.toMeasure.map f=q.toMeasure.map f) (F : B → ℝ) :
    pmfMean p (fun a => F (f a))=pmfMean q (fun a => F (f a)) := by
  apply pmfMean_comp_eq_of_map_eq p q f _ F
  apply PMF.toMeasure_injective
  rw [←PMF.toMeasure_map f p (measurable_of_countable _),
    ←PMF.toMeasure_map f q (measurable_of_countable _)]
  exact he

end
end SecondOrder
