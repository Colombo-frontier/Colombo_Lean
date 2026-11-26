import FreshGradientMinimax.QuadraticFiber

/-! Integrability and expectation transport through the actual joint law
of an input and the following kernel output. No independence is required. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem comap_comp_measure (K : Kernel Y Z) (f : X → Y) (hf : Measurable f) (ν : Measure X) :
    K.comap f hf ∘ₘ ν = K ∘ₘ ν.map f := by
  rw [← Measure.deterministic_comp_eq_map hf, Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]

theorem adjacent_moment_bound (ν : Measure X) [IsProbabilityMeasure ν]
    (K : Kernel X Y) [IsMarkovKernel K]
    (A : X → ℝ) (hA : Measurable A) (B P : Y → ℝ) (hB : Measurable B) (hP : Measurable P)
    (hPpos : ∀ y, 0 ≤ P y) (hAi : Integrable A ν) (hBi : Integrable B (K ∘ₘ ν))
    (hbound : ∀ᵐ p ∂ν ⊗ₘ K, P p.2 ≤ A p.1 + B p.2) :
    Integrable P (K ∘ₘ ν) ∧ (∫ y, P y ∂K ∘ₘ ν) ≤ (∫ x, A x ∂ν) + ∫ y, B y ∂K ∘ₘ ν := by
  have hfst : (ν ⊗ₘ K).map Prod.fst = ν := Measure.fst_compProd ν K
  have hsnd : (ν ⊗ₘ K).map Prod.snd = K ∘ₘ ν := Measure.snd_compProd ν K
  have hAi' : Integrable (fun p : X × Y => A p.1) (ν ⊗ₘ K) := by
    apply (integrable_map_measure hA.stronglyMeasurable.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [hfst]
  have hBi' : Integrable (fun p : X × Y => B p.2) (ν ⊗ₘ K) := by
    apply (integrable_map_measure hB.stronglyMeasurable.aestronglyMeasurable measurable_snd.aemeasurable).mp
    rwa [hsnd]
  have hPi' : Integrable (fun p : X × Y => P p.2) (ν ⊗ₘ K) := by
    apply (hAi'.add hBi').mono' (hP.comp measurable_snd).aestronglyMeasurable
    filter_upwards [hbound] with p hp
    simpa only [Function.comp_apply, Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (hPpos p.2)] using hp
  have hAiEq : (∫ p : X × Y, A p.1 ∂ν ⊗ₘ K) = ∫ x, A x ∂ν := by
    conv_rhs => rw [← hfst]
    rw [integral_map measurable_fst.aemeasurable hA.stronglyMeasurable.aestronglyMeasurable]
  have hBiEq : (∫ p : X × Y, B p.2 ∂ν ⊗ₘ K) = ∫ y, B y ∂K ∘ₘ ν := by
    conv_rhs => rw [← hsnd]
    rw [integral_map measurable_snd.aemeasurable hB.stronglyMeasurable.aestronglyMeasurable]
  have hPiEq : (∫ p : X × Y, P p.2 ∂ν ⊗ₘ K) = ∫ y, P y ∂K ∘ₘ ν := by
    conv_rhs => rw [← hsnd]
    rw [integral_map measurable_snd.aemeasurable hP.stronglyMeasurable.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · rw [← hsnd]
    exact (integrable_map_measure hP.stronglyMeasurable.aestronglyMeasurable measurable_snd.aemeasurable).mpr hPi'
  · have h := integral_mono_ae hPi' (hAi'.add hBi') hbound
    simp only [Pi.add_apply] at h
    rw [integral_add hAi' hBi', hAiEq, hBiEq, hPiEq] at h
    exact h

end FreshGradientMinimax
