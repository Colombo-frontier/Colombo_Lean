import RandomizedFO2003.FiniteBlockProbability

namespace RandomizedFO2003

open MeasureTheory
open scoped BigOperators

/-- Replacing one coordinate of an independent finite product by a fresh
sample with the same law preserves the original full product law. The
unused old coordinate is allowed to remain in the independent background. -/
theorem pi_refresh_preserving {I X : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace X]
    (σ : Measure X) [IsProbabilityMeasure σ] (i : I) :
    MeasurePreserving (fun p : X × (I → X) => Function.update p.2 i p.1)
      (σ.prod (Measure.pi (fun _ : I => σ))) (Measure.pi (fun _ : I => σ)) := by
  classical
  have hf : Measurable (fun p : X × (I → X) => Function.update p.2 i p.1) := by
    apply measurable_pi_lambda
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using (measurable_fst : Measurable (fun p : X × (I → X) => p.1))
    · simpa only [Function.update_of_ne hji] using (measurable_pi_apply j).comp measurable_snd
  refine ⟨hf, (Measure.pi_eq (fun s hs => ?_)).symm⟩
  rw [Measure.map_apply hf (MeasurableSet.pi Set.countable_univ (fun j _ => hs j))]
  have hpre : (fun p : X × (I → X) => Function.update p.2 i p.1) ⁻¹' Set.univ.pi s =
      s i ×ˢ Set.univ.pi (Function.update s i Set.univ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ_pi]
    constructor
    · intro hp
      refine ⟨by simpa only [Function.update_self] using hp i, ?_⟩
      intro j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self, Set.mem_univ]
      · simpa only [Function.update_of_ne hji] using hp j
    · rintro ⟨hi, hp⟩ j
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using hi
      · simpa only [Function.update_of_ne hji] using hp j
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hprod : (∏ j : I, σ (Function.update s i Set.univ j)) =
      ∏ j ∈ Finset.univ.erase i, σ (s j) := by
    rw [← Finset.prod_erase_mul Finset.univ (fun j => σ (Function.update s i Set.univ j)) (Finset.mem_univ i)]
    simp only [Function.update_self, measure_univ, mul_one]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hprod]
  exact Finset.mul_prod_erase Finset.univ (fun j => σ (s j)) (Finset.mem_univ i)

end RandomizedFO2003
