import SecondOrder.FiniteAdaptiveLaw
import SecondOrder.FiniteEventInformation

open scoped BigOperators Classical

universe u

namespace SecondOrder
noncomputable section
variable {H S U A : Type u} [Fintype H] [Fintype S] [Fintype U] [Fintype A]

def finiteHistoryMapInitial (f : S → U) : (n : ℕ) → FiniteHistory S A n → FiniteHistory U A n
  | 0, h => f h
  | n+1, h => (finiteHistoryMapInitial f n h.1,h.2)

/-- A transition which cannot inspect the hidden component of the initial
state. Its dependence on the entire observed coefficient history is retained. -/
def hiddenIndependentTransition (K : ∀ n, FiniteHistory S A n → PMF A)
    (n : ℕ) (h : FiniteHistory (H × S) A n) : PMF A :=
  K n (finiteHistoryMapInitial Prod.snd n h)

/-- Reference sampling remains independent of the hidden variable even after
arbitrarily many history-dependent transitions. This is a factorization of
the actual joint law, not an assumed conditional independence. -/
theorem finiteAdaptiveLaw_hidden_independent (μ : PMF H) (p : PMF S)
    (K : ∀ n, FiniteHistory S A n → PMF A) :
    ∀ n (F : H → FiniteHistory S A n → ℝ),
      pmfMean (finiteAdaptiveLaw (finiteProdPMF μ p) (hiddenIndependentTransition K) n)
        (fun h => F (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)) =
      pmfMean μ (fun θ => pmfMean (finiteAdaptiveLaw p K n) (F θ)) := by
  intro n
  induction n with
  | zero =>
    intro F
    change pmfMean (finiteProdPMF μ p) (fun h => F h.1 h.2)=_
    simp only [pmfMean, smul_eq_mul, finiteProdPMF_apply, ENNReal.toReal_mul,
      Fintype.sum_prod_type, Finset.mul_sum, mul_assoc, finiteAdaptiveLaw_zero]
    apply Finset.sum_congr (by ext; simp)
    intro θ _
    apply Finset.sum_congr (by ext; simp)
    intro h _
    rfl
  | succ n ih =>
    intro F
    change pmfMean (finiteConditionalPMF _ _) (fun h =>
      F (finiteHistoryInitial n h.1).1 (finiteHistoryMapInitial Prod.snd n h.1,h.2))=_
    rw [finiteConditionalPMF_mean]
    change pmfMean (finiteAdaptiveLaw (finiteProdPMF μ p) (hiddenIndependentTransition K) n)
      (fun h => pmfMean (K n (finiteHistoryMapInitial Prod.snd n h))
        (fun a => F (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h,a)))=_
    rw [ih (fun θ h => pmfMean (K n h) (fun a => F θ (h,a)))]
    apply pmfMean_congr
    intro θ
    exact (finiteConditionalPMF_mean (finiteAdaptiveLaw p K n) (K n) (fun h => F θ h)).symm

theorem pmfMean_comm (μ : PMF H) (p : PMF S) (F : H → S → ℝ) :
    pmfMean μ (fun θ => pmfMean p (F θ))=pmfMean p (fun h => pmfMean μ (fun θ => F θ h)) := by
  simp only [pmfMean, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro θ _
  ring

/-- Arbitrary query maps of the reference transcript inherit the independent
hidden-vector tail bound. -/
theorem finiteReferenceEvent_probability (μ : PMF H) (p : PMF S)
    (K : ∀ n, FiniteHistory S A n → PMF A) (n : ℕ)
    (E : H → FiniteHistory S A n → Bool) {q : ℝ}
    (hE : ∀ h, pmfEventProbability μ (fun θ => E θ h)≤q) :
    pmfEventProbability (finiteAdaptiveLaw (finiteProdPMF μ p) (hiddenIndependentTransition K) n)
      (fun h => E (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h))≤q := by
  rw [pmfEventProbability_mean,
    finiteAdaptiveLaw_hidden_independent μ p K n (fun θ h => if E θ h=true then 1 else 0), pmfMean_comm]
  apply pmfMean_le_const
  intro h
  exact (pmfEventProbability_mean μ (fun θ => E θ h)).symm ▸ hE h

end
end SecondOrder
