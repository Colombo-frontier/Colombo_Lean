import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace SecondOrder
noncomputable section
variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace H]

/-- Replacing a single coordinate by a fresh sample from its own marginal
preserves the complete independent hidden prior. -/
theorem independent_coordinate_refresh (ρ : ι → Measure H) [∀ i, IsProbabilityMeasure (ρ i)] (j : ι) :
    ((Measure.pi ρ).prod (ρ j)).map (fun z => Function.update z.1 j z.2) = Measure.pi ρ := by
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have he : (fun z : (ι → H) × H => Function.update z.1 j z.2) ⁻¹' Set.pi Set.univ s =
      (Set.pi Set.univ (Function.update s j Set.univ)) ×ˢ s j := by
    ext z
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,true_implies,Set.mem_prod]
    constructor
    · intro hz
      refine ⟨?_,?_⟩
      · intro i
        by_cases hi : i=j
        · subst i; simp
        · simpa only [Function.update_of_ne hi] using hz i
      · simpa only [Function.update_self] using hz j
    · rintro ⟨hz,hj⟩ i
      by_cases hi : i=j
      · subst i; simpa only [Function.update_self] using hj
      · simpa only [Function.update_of_ne hi] using hz i
  rw [he,Measure.prod_prod,Measure.pi_pi]
  have hf : (fun i => ρ i (Function.update s j Set.univ i)) =
      Function.update (fun i => ρ i (s i)) j 1 := by
    funext i
    by_cases hi : i=j
    · subst i; simp only [Function.update_self,measure_univ]
    · simp only [Function.update_of_ne hi]
  rw [hf,Finset.prod_update_of_mem (Finset.mem_univ j),one_mul,Finset.sdiff_singleton_eq_erase,
    Finset.prod_erase_mul _ _ (Finset.mem_univ j)]

theorem lintegral_independent_coordinate_refresh (ρ : ι → Measure H)
    [∀ i, IsProbabilityMeasure (ρ i)] (j : ι) {F : (ι → H) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ Θ, ∫⁻ θ, F (Function.update Θ j θ) ∂ρ j ∂Measure.pi ρ) = ∫⁻ Θ, F Θ ∂Measure.pi ρ := by
  have hm : Measurable (fun z : (ι → H) × H => F (Function.update z.1 j z.2)) :=
    hF.comp measurable_update'
  calc
    _ = ∫⁻ z, F (Function.update z.1 j z.2) ∂(Measure.pi ρ).prod (ρ j) := (lintegral_prod _ hm.aemeasurable).symm
    _ = ∫⁻ Θ, F Θ ∂(((Measure.pi ρ).prod (ρ j)).map (fun z => Function.update z.1 j z.2)) :=
      (lintegral_map hF measurable_update').symm
    _ = _ := by rw [independent_coordinate_refresh ρ j]

end
end SecondOrder
