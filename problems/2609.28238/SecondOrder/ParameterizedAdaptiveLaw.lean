import SecondOrder.FiniteStoppingTape

open scoped Classical

namespace SecondOrder
noncomputable section
variable {H S A : Type} [Fintype H] [Fintype S] [Fintype A]

def parameterizedTransition (K : H → ∀ n, FiniteHistory S A n → PMF A)
    (n : ℕ) (h : FiniteHistory (H × S) A n) : PMF A :=
  K (finiteHistoryInitial n h).1 n (finiteHistoryMapInitial Prod.snd n h)

/-- Sampling the hidden parameter first and then running its own adaptive
law equals retaining the parameter in the initial joint state. -/
theorem finiteAdaptiveLaw_parameter_mean (μ : PMF H) (p : PMF S)
    (K : H → ∀ n, FiniteHistory S A n → PMF A) :
    ∀ n (F : H → FiniteHistory S A n → ℝ),
    pmfMean (finiteAdaptiveLaw (finiteProdPMF μ p) (parameterizedTransition K) n)
      (fun h => F (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h))=
      pmfMean μ (fun θ => pmfMean (finiteAdaptiveLaw p (K θ) n) (F θ)) := by
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
    change pmfMean (finiteAdaptiveLaw (finiteProdPMF μ p) (parameterizedTransition K) n)
      (fun h => pmfMean (K (finiteHistoryInitial n h).1 n (finiteHistoryMapInitial Prod.snd n h))
        (fun a => F (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h,a)))=_
    rw [ih (fun θ h => pmfMean (K θ n h) (fun a => F θ (h,a)))]
    apply pmfMean_congr
    intro θ
    exact (finiteConditionalPMF_mean (finiteAdaptiveLaw p (K θ) n) (K θ n) (fun h => F θ h)).symm

theorem cappedTransition_parameter (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ)
    (K D : H → ∀ n, FiniteHistory S A n → PMF A) :
    cappedTransition (fun n h => select n (finiteHistoryMapInitial Prod.snd n h)) cap
      (parameterizedTransition K) (parameterizedTransition D)=
      parameterizedTransition (fun θ => cappedTransition select cap (K θ) (D θ)) := by
  funext n h
  unfold cappedTransition parameterizedTransition
  rw [cappedHistoryCount_hidden]

end
end SecondOrder
