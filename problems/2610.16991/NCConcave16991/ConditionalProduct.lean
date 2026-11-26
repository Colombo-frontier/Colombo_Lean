import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fresh independent samples conditional on a complete history

On a genuine product probability space, conditioning on the first coordinate
integrates the fresh second coordinate. The proof uses the defining set-
integral characterization of conditional expectation and Fubini's theorem.
-/

open Set MeasureTheory
open scoped Topology

namespace NCConcave16991

variable {Ω I H : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace I]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

theorem conditional_product_integral (μ : Measure Ω) (ν : Measure I)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : Ω × I → H} (hFm : StronglyMeasurable F) (hF : Integrable F (μ.prod ν)) :
    (μ.prod ν)[F | mΩ.comap (Prod.fst : Ω × I → Ω)] =ᵐ[μ.prod ν]
      fun a ↦ ∫ i, F (a.1, i) ∂ν := by
  have hm : mΩ.comap (Prod.fst : Ω × I → Ω) ≤ (inferInstance : MeasurableSpace (Ω × I)) :=
    (measurable_fst : Measurable (Prod.fst : Ω × I → Ω)).comap_le
  let g : Ω → H := fun ω ↦ ∫ i, F (ω, i) ∂ν
  have hg : Integrable (fun a : Ω × I ↦ g a.1) (μ.prod ν) :=
    hF.integral_prod_left.comp_fst ν
  have hgsm : StronglyMeasurable[mΩ.comap (Prod.fst : Ω × I → Ω)] (fun a : Ω × I ↦ g a.1) := by
    have hfst : Measurable[mΩ.comap (Prod.fst : Ω × I → Ω)] (Prod.fst : Ω × I → Ω) :=
      measurable_iff_comap_le.mpr le_rfl
    exact hFm.integral_prod_right'.comp_measurable hfst
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hF
    (fun s hs hfin ↦ hg.integrableOn) _ hgsm.aestronglyMeasurable
  intro s hs hfin
  change ∃ s0 : Set Ω, MeasurableSet s0 ∧ (Prod.fst : Ω × I → Ω) ⁻¹' s0 = s at hs
  obtain ⟨s0, hs0, rfl⟩ := hs
  have hset : (Prod.fst : Ω × I → Ω) ⁻¹' s0 = s0 ×ˢ univ := by ext a; simp
  rw [hset]
  have hf0 : Integrable F ((μ.restrict s0).prod ν) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hF.integrableOn
  have hg0 : Integrable (fun a : Ω × I ↦ g a.1) ((μ.restrict s0).prod ν) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hg.integrableOn
  change (∫ a, g a.1 ∂(μ.prod ν).restrict (s0 ×ˢ univ)) =
    ∫ a, F a ∂(μ.prod ν).restrict (s0 ×ˢ univ)
  rw [← Measure.restrict_prod_eq_prod_univ, integral_prod _ hg0, integral_prod _ hf0]
  apply integral_congr_ae
  filter_upwards with ω
  simp [g]

end NCConcave16991
