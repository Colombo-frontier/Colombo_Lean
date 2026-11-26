import SecondOrder.SeededQueryPolicy

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

instance finiteHistoryMeasurableSpace {S A : Type u} [MeasurableSpace S] [MeasurableSpace A] (n : ℕ) :
    MeasurableSpace (FiniteHistory S A n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace S)
  | succ n ih => exact @Prod.instMeasurableSpace _ _ ih inferInstance

instance finiteHistoryMeasurableSingleton {S A : Type u} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSingletonClass S] [MeasurableSingletonClass A] (n : ℕ) :
    MeasurableSingletonClass (FiniteHistory S A n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSingletonClass S)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (MeasurableSingletonClass (FiniteHistory S A n × A))

variable {Ξ A : Type*} [MeasurableSpace Ξ] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

theorem finiteSeed_event_measurable (E : Ξ → A → Prop) (hE : ∀ a, MeasurableSet {ξ | E ξ a}) :
    MeasurableSet {w : Ξ × A | E w.1 w.2} := by
  have he : {w : Ξ × A | E w.1 w.2}=⋃ a, {ξ | E ξ a} ×ˢ {a} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · intro hw; exact ⟨w.2,hw,rfl⟩
    · rintro ⟨a,hw,ha⟩; simpa only [ha] using hw
  rw [he]
  exact MeasurableSet.iUnion (fun a => (hE a).prod (measurableSet_singleton a))

/-- The seed average is the actual probability under independent private
randomness and finite oracle samples, not a surrogate success criterion. -/
theorem finiteSeed_probability_eq_integral (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (p : PMF A) (E : Ξ → A → Prop) (hE : ∀ a, MeasurableSet {ξ | E ξ a}) :
    (μ.prod p.toMeasure).real {w : Ξ × A | E w.1 w.2}=
      ∫ ξ, pmfEventProbability p (fun a => decide (E ξ a)) ∂μ := by
  have he := finiteSeed_event_measurable E hE
  have hi : Integrable (fun w : Ξ × A => if E w.1 w.2 then (1:ℝ) else 0) (μ.prod p.toMeasure) := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      (integrable_const (1:ℝ) (μ := μ.prod p.toMeasure)).indicator he
  rw [←integral_indicator_one he]
  simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    simp only [PMF.integral_eq_sum, pmfEventProbability_mean, pmfMean,
      Set.indicator, Set.mem_setOf_eq, Pi.one_apply, decide_eq_true_eq])

end
end SecondOrder
