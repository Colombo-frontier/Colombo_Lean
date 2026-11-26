import SecondOrder.ComparisonRestartLaw

open scoped Classical

namespace SecondOrder
noncomputable section
variable {H S A : Type} [Fintype H] [Fintype S] [Fintype A]

theorem pmfMean_ite_zero {B : Type*} [Fintype B] (p : PMF B) (E : Prop) (F : B → ℝ) :
    pmfMean p (fun b => if E then F b else 0)=if E then pmfMean p F else 0 := by
  by_cases h : E
  · simp only [if_pos h]
  · simp only [if_neg h, pmfMean_const]

/-- Exact conditional continuation formula on a hidden-independent entry
slice. All future adaptivity and dependence on the entry history are retained. -/
theorem finiteHiddenContinuation_mean (μ : PMF H) (p : PMF S)
    (K : H → ∀ n, FiniteHistory S A n → PMF A) (θ₀ : H) (n k : ℕ)
    (E : H → FiniteHistory S A n → Prop) (F : H → FiniteHistory S A (n+k) → ℝ)
    (hE : ∀ θ h, E θ h ↔ E θ₀ h)
    (hK : ∀ θ h, E θ₀ h → finiteAdaptiveLaw p (K θ) n h=finiteAdaptiveLaw p (K θ₀) n h) :
    pmfMean (finiteConditionalPMF μ (fun θ => finiteAdaptiveLaw p (K θ) (n+k)))
      (fun w => if E w.1 (finiteHistoryPrefix n k w.2) then F w.1 w.2 else 0)=
      pmfMean (finiteAdaptiveLaw p (K θ₀) n) (fun h => if E θ₀ h then
        pmfMean μ (fun θ => pmfMean (finiteContinuationLaw (K θ) n h k)
          (fun u => F θ (finiteHistoryAppend n h k u))) else 0) := by
  rw [finiteConditionalPMF_mean]
  simp_rw [finiteAdaptiveLaw_continuation_mean p (K _) n k,
    finiteHistoryPrefix_append, pmfMean_ite_zero]
  have hh := finiteHiddenSlice_mean μ (fun θ => finiteAdaptiveLaw p (K θ) n) θ₀ E
    (fun θ h => pmfMean (finiteContinuationLaw (K θ) n h k)
      (fun u => F θ (finiteHistoryAppend n h k u))) hE hK
  rw [finiteConditionalPMF_mean] at hh
  exact hh

theorem finiteHiddenContinuation_probability_le (μ : PMF H) (p : PMF S)
    (K : H → ∀ n, FiniteHistory S A n → PMF A) (θ₀ : H) (n k : ℕ)
    (E : H → FiniteHistory S A n → Prop) (F : H → FiniteHistory S A (n+k) → Prop)
    (hE : ∀ θ h, E θ h ↔ E θ₀ h)
    (hK : ∀ θ h, E θ₀ h → finiteAdaptiveLaw p (K θ) n h=finiteAdaptiveLaw p (K θ₀) n h)
    {q : ℝ} (hfuture : ∀ h, E θ₀ h →
      pmfMean μ (fun θ => pmfEventProbability (finiteContinuationLaw (K θ) n h k)
        (fun u => decide (F θ (finiteHistoryAppend n h k u))))≤q) :
    pmfEventProbability (finiteConditionalPMF μ (fun θ => finiteAdaptiveLaw p (K θ) (n+k)))
      (fun w => decide (E w.1 (finiteHistoryPrefix n k w.2) ∧ F w.1 w.2))≤
      q*pmfEventProbability (finiteAdaptiveLaw p (K θ₀) n) (fun h => decide (E θ₀ h)) := by
  rw [pmfEventProbability_mean]
  simp only [decide_eq_true_eq, ite_and]
  rw [finiteHiddenContinuation_mean μ p K θ₀ n k E (fun θ h => if F θ h then 1 else 0) hE hK,
    pmfEventProbability_mean, ←pmfMean_mul]
  apply pmfMean_mono
  intro h
  by_cases he : E θ₀ h
  · simp only [if_pos he, decide_eq_true_eq, mul_one]
    simpa only [pmfEventProbability_mean, decide_eq_true_eq] using hfuture h he
  · simp only [if_neg he, decide_eq_true_eq, mul_zero, le_refl]

end
end SecondOrder
