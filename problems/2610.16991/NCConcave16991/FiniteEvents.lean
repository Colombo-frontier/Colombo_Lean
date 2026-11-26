import NCConcave16991.FiniteFailure
import Mathlib.MeasureTheory.Integral.Prod

/-! # Probabilities of actual events under finite product laws -/

open Set MeasureTheory

namespace NCConcave16991

noncomputable section

variable {Ω I : Type*} [Finite Ω] [Finite I]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  (μ : Measure Ω) (ν : Measure I) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem product_event_probability (E : Set (Ω × I)) :
    (μ.prod ν).real E = ∫ ω, ν.real {i | (ω, i) ∈ E} ∂μ := by
  classical
  have hE : MeasurableSet E := (Set.to_countable _).measurableSet
  rw [← integral_indicator_one hE, integral_prod _ Integrable.of_finite]
  apply integral_congr_ae
  filter_upwards with ω
  have he : (fun i ↦ E.indicator (1 : Ω × I → ℝ) (ω, i)) =
      {i | (ω, i) ∈ E}.indicator (1 : I → ℝ) := by
    funext i
    simp only [Set.indicator_apply, mem_setOf_eq, Pi.one_apply]
  rw [he]
  exact integral_indicator_one ((Set.to_countable _).measurableSet)

theorem product_event_probability_le (E : Set (Ω × I)) {p : ℝ}
    (h : ∀ ω, ν.real {i | (ω, i) ∈ E} ≤ p) : (μ.prod ν).real E ≤ p := by
  rw [product_event_probability]
  have hh := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite h
  simpa only [integral_const, probReal_univ, one_smul] using hh

theorem product_fst_event_probability (E : Set Ω) :
    (μ.prod ν).real {a | a.1 ∈ E} = μ.real E := by
  classical
  rw [product_event_probability]
  change (∫ ω, ν.real {i : I | ω ∈ E} ∂μ) = μ.real E
  have he (ω : Ω) : ν.real {i : I | ω ∈ E} = E.indicator (1 : Ω → ℝ) ω := by
    by_cases h : ω ∈ E <;> simp [h, Set.indicator]
  simp_rw [he]
  exact integral_indicator_one ((Set.to_countable _).measurableSet)

end

end NCConcave16991
