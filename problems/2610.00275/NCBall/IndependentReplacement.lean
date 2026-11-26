import NCBall.GaussianQueryStep

/-! # Resampling one room without changing the joint experiment law -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NCBall

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

omit [Fintype ι] in
theorem independent_replacement_measurable (j : ι) :
    Measurable (fun wz : (ι → E) × E => Function.update wz.1 j wz.2) := by
  classical
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = j
  · subst i
    simpa only [Function.update_self] using (measurable_snd : Measurable (Prod.snd : (ι → E) × E → E))
  · simpa only [Function.update_of_ne hi] using (measurable_pi_apply i).comp measurable_fst

theorem independent_replacement_law (μ : Measure E) [IsProbabilityMeasure μ] (j : ι) :
    ((Measure.pi (fun _ : ι => μ)).prod μ).map
      (fun wz : (ι → E) × E => Function.update wz.1 j wz.2) = Measure.pi (fun _ : ι => μ) := by
  classical
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (independent_replacement_measurable j) (MeasurableSet.univ_pi hs)]
  have he : (fun wz : (ι → E) × E => Function.update wz.1 j wz.2) ⁻¹' pi univ s =
      (pi univ (Function.update s j univ)) ×ˢ s j := by
    ext ⟨w, z⟩
    simp only [mem_preimage, mem_univ_pi, mem_prod]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro i
        by_cases hi : i = j
        · subst i
          simp
        · simpa only [Function.update_of_ne hi] using h i
      · simpa only [Function.update_self] using h j
    · rintro ⟨hw, hz⟩ i
      by_cases hi : i = j
      · subst i
        simpa only [Function.update_self] using hz
      · simpa only [Function.update_of_ne hi] using hw i
  rw [he, Measure.prod_prod, Measure.pi_pi]
  have hf : (fun i => μ (Function.update s j univ i)) = Function.update (fun i => μ (s i)) j 1 := by
    funext i
    by_cases hi : i = j
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ j), one_mul]
  simpa only [Finset.sdiff_singleton_eq_erase] using
    Finset.prod_erase_mul _ (fun i => μ (s i)) (Finset.mem_univ j)

theorem independent_replacement_with_seed {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι) :
    (((ν.prod (Measure.pi (fun _ : ι => μ))).prod μ)).map
      (fun sw : (S × (ι → E)) × E => (sw.1.1, Function.update sw.1.2 j sw.2)) =
      ν.prod (Measure.pi (fun _ : ι => μ)) := by
  let P := Measure.pi (fun _ : ι => μ)
  let f := fun wz : (ι → E) × E => Function.update wz.1 j wz.2
  have hf : Measurable f := independent_replacement_measurable j
  have he : Measurable (Prod.map (id : S → S) f) := measurable_id.prodMap hf
  let e : ((S × (ι → E)) × E) ≃ᵐ (S × ((ι → E) × E)) := MeasurableEquiv.prodAssoc
  calc
    _ = (((ν.prod P).prod μ).map e).map (Prod.map id f) := by
      rw [Measure.map_map he e.measurable]
      rfl
    _ = (ν.prod (P.prod μ)).map (Prod.map id f) := by rw [show e = MeasurableEquiv.prodAssoc from rfl, Measure.prodAssoc_prod]
    _ = (ν.map id).prod ((P.prod μ).map f) := (Measure.map_prod_map _ _ measurable_id hf).symm
    _ = _ := by rw [Measure.map_id, independent_replacement_law]

end NCBall
