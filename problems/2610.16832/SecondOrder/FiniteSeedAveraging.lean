import SecondOrder.CurvatureSequentialLowerBound

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {Ξ H A : Type*} [MeasurableSpace Ξ] [Fintype H] [Fintype A]

theorem integrable_pmfMean (μ : Measure Ξ) (p : PMF A) (F : Ξ → A → ℝ)
    (hF : ∀ a, Integrable (fun ξ => F ξ a) μ) :
    Integrable (fun ξ => pmfMean p (F ξ)) μ := by
  change Integrable (fun ξ => ∑ a, (p a).toReal * F ξ a) μ
  exact integrable_finset_sum _ (fun a _ => (hF a).const_mul (p a).toReal)

theorem integral_pmfMean (μ : Measure Ξ) (p : PMF A) (F : Ξ → A → ℝ)
    (hF : ∀ a, Integrable (fun ξ => F ξ a) μ) :
    (∫ ξ, pmfMean p (F ξ) ∂μ)=pmfMean p (fun a => ∫ ξ, F ξ a ∂μ) := by
  simp only [pmfMean, smul_eq_mul]
  rw [integral_finset_sum Finset.univ (fun a _ => (hF a).const_mul (p a).toReal)]
  simp only [integral_const_mul]

theorem integrable_pmfEventProbability (μ : Measure Ξ) [IsFiniteMeasure μ]
    (p : PMF A) (E : Ξ → A → Prop) (hE : ∀ a, MeasurableSet {ξ | E ξ a}) :
    Integrable (fun ξ => pmfEventProbability p (fun a => decide (E ξ a))) μ := by
  simp only [pmfEventProbability_mean, decide_eq_true_eq]
  apply integrable_pmfMean
  intro a
  simpa only [Set.indicator, Set.mem_setOf_eq] using
    (integrable_const (1:ℝ)).indicator (hE a)

/-- Average the private seed before choosing the finite hidden instance. This
retains one common target for the whole randomized algorithm. -/
theorem finiteSeed_hidden_mean_le (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (prior : PMF H) (law : H → PMF A) (E : Ξ → H → A → Prop)
    (hE : ∀ θ a, MeasurableSet {ξ | E ξ θ a}) {b : ℝ}
    (hbound : ∀ ξ, pmfMean prior (fun θ => pmfEventProbability (law θ) (fun a => decide (E ξ θ a)))≤b) :
    pmfMean prior (fun θ => ∫ ξ, pmfEventProbability (law θ) (fun a => decide (E ξ θ a)) ∂μ)≤b := by
  have hi (θ : H) := integrable_pmfEventProbability μ (law θ) (fun ξ a => E ξ θ a) (hE θ)
  rw [←integral_pmfMean μ prior _ hi]
  have hh := integral_mono (integrable_pmfMean μ prior _ hi) (integrable_const b) hbound
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hh

theorem finiteSeed_exists_hard_instance (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (prior : PMF H) (law : H → PMF A) (E : Ξ → H → A → Prop)
    (hE : ∀ θ a, MeasurableSet {ξ | E ξ θ a}) {b c : ℝ} (hbc : b<c)
    (hbound : ∀ ξ, pmfMean prior (fun θ => pmfEventProbability (law θ) (fun a => decide (E ξ θ a)))≤b) :
    ∃ θ, (∫ ξ, pmfEventProbability (law θ) (fun a => decide (E ξ θ a)) ∂μ)<c :=
  exists_below_pmfMean_bound prior _ (lt_of_le_of_lt (finiteSeed_hidden_mean_le μ prior law E hE hbound) hbc)

end
end SecondOrder
