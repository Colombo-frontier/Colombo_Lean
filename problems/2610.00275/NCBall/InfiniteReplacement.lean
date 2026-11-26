import NCBall.CountablePool
import NCBall.IndependentReplacement

/-! # Refreshing one coordinate in an infinite iid sample pool preserves its law -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NCBall

theorem infinite_replacement_law {ι Z : Type*} [DecidableEq ι] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (j : ι) :
    ((Measure.infinitePi (fun _ : ι => μ)).prod μ).map
      (fun wz : (ι → Z) × Z => Function.update wz.1 j wz.2) =
      Measure.infinitePi (fun _ : ι => μ) := by
  classical
  apply Measure.eq_infinitePi
  intro s A hA
  rw [Measure.map_apply (independent_replacement_measurable j) (MeasurableSet.pi s.countable_toSet hA)]
  by_cases hj : j ∈ s
  · have he : (fun wz : (ι → Z) × Z => Function.update wz.1 j wz.2) ⁻¹' pi (s : Set ι) A =
        (pi (s.erase j : Set ι) A) ×ˢ A j := by
      ext ⟨w, z⟩
      simp only [mem_preimage, mem_pi, Finset.mem_coe, mem_prod]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · intro i hi
          simpa only [Function.update_of_ne (Finset.mem_erase.mp hi).1] using
            h i (Finset.mem_erase.mp hi).2
        · simpa only [Function.update_self] using h j hj
      · rintro ⟨hw, hz⟩ i hi
        by_cases hij : i = j
        · subst i
          simpa only [Function.update_self] using hz
        · simpa only [Function.update_of_ne hij] using hw i (Finset.mem_erase.mpr ⟨hij, hi⟩)
    rw [he, Measure.prod_prod, Measure.infinitePi_pi (fun _ : ι => μ) (fun i hi => hA i (Finset.mem_erase.mp hi).2)]
    exact Finset.prod_erase_mul _ (fun i => μ (A i)) hj
  · have he : (fun wz : (ι → Z) × Z => Function.update wz.1 j wz.2) ⁻¹' pi (s : Set ι) A =
        (pi (s : Set ι) A) ×ˢ univ := by
      ext ⟨w, z⟩
      simp only [mem_preimage, mem_pi, Finset.mem_coe, mem_prod, mem_univ, and_true]
      constructor <;> intro h i hi
      · simpa only [Function.update_of_ne (show i ≠ j by intro he; subst i; exact hj hi)] using h i hi
      · simpa only [Function.update_of_ne (show i ≠ j by intro he; subst i; exact hj hi)] using h i hi
    rw [he, Measure.prod_prod, Measure.infinitePi_pi (fun _ : ι => μ) hA, measure_univ, mul_one]

theorem infinite_replacement_with_seed {S ι Z : Type*} [DecidableEq ι] [MeasurableSpace S] [MeasurableSpace Z]
    (ν : Measure S) [IsProbabilityMeasure ν] (μ : Measure Z) [IsProbabilityMeasure μ] (j : ι) :
    MeasurePreserving (fun sw : (S × (ι → Z)) × Z => (sw.1.1, Function.update sw.1.2 j sw.2))
      ((ν.prod (Measure.infinitePi (fun _ : ι => μ))).prod μ)
      (ν.prod (Measure.infinitePi (fun _ : ι => μ))) := by
  classical
  have h1 := measurePreserving_prodAssoc ν (Measure.infinitePi (fun _ : ι => μ)) μ
  have h2 := (MeasurePreserving.id ν).prod
    (show MeasurePreserving (fun wz : (ι → Z) × Z => Function.update wz.1 j wz.2)
      ((Measure.infinitePi (fun _ : ι => μ)).prod μ) (Measure.infinitePi (fun _ : ι => μ)) from
        ⟨independent_replacement_measurable j, infinite_replacement_law μ j⟩)
  exact h2.comp h1

end NCBall
