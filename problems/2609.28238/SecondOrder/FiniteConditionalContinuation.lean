import SecondOrder.FiniteHistoryAppend

open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {S A : Type} [Fintype S] [Fintype A]

def finiteContinuationTransition (K : ∀ n, FiniteHistory S A n → PMF A)
    (n : ℕ) (h : FiniteHistory S A n) (k : ℕ) (u : FiniteHistory Unit A k) : PMF A :=
  K (n+k) (finiteHistoryAppend n h k u)

def finiteContinuationLaw (K : ∀ n, FiniteHistory S A n → PMF A)
    (n : ℕ) (h : FiniteHistory S A n) (k : ℕ) : PMF (FiniteHistory Unit A k) :=
  finiteAdaptiveLaw (PMF.pure ()) (finiteContinuationTransition K n h) k

/-- Exact factorization of the original mass into prefix mass and the actual
fresh continuation mass. It also holds when the prefix has probability zero. -/
theorem finiteAdaptiveLaw_append_mass (p : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A)
    (n : ℕ) (h : FiniteHistory S A n) : ∀ k u,
    finiteAdaptiveLaw p K (n+k) (finiteHistoryAppend n h k u)=
      finiteAdaptiveLaw p K n h*finiteContinuationLaw K n h k u := by
  intro k
  induction k with
  | zero => intro u; cases u; simp [finiteContinuationLaw, finiteHistoryAppend]
  | succ k ih =>
    intro u
    change finiteAdaptiveLaw p K (n+k) (finiteHistoryAppend n h k u.1)*
      K (n+k) (finiteHistoryAppend n h k u.1) u.2=
      finiteAdaptiveLaw p K n h*(finiteContinuationLaw K n h k u.1*
        K (n+k) (finiteHistoryAppend n h k u.1) u.2)
    rw [ih, mul_assoc]

/-- The tower formula for arbitrary adaptive finite histories, conditioning
on a fixed prefix and retaining all dependence on that prefix. -/
theorem finiteAdaptiveLaw_continuation_mean (p : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A)
    (n : ℕ) : ∀ k (F : FiniteHistory S A (n+k) → ℝ),
    pmfMean (finiteAdaptiveLaw p K (n+k)) F=
      pmfMean (finiteAdaptiveLaw p K n)
        (fun h => pmfMean (finiteContinuationLaw K n h k) (fun u => F (finiteHistoryAppend n h k u))) := by
  intro k
  induction k with
  | zero =>
    intro F
    change pmfMean (finiteAdaptiveLaw p K n) F=
      pmfMean (finiteAdaptiveLaw p K n) (fun h => pmfMean (PMF.pure ()) (fun _ : Unit => F h))
    simp only [pmfMean_const]
  | succ k ih =>
    intro F
    change pmfMean (finiteConditionalPMF _ _) F=_
    rw [finiteConditionalPMF_mean]
    change pmfMean (finiteAdaptiveLaw p K (n+k))
      (fun h => pmfMean (K (n+k) h) (fun a => F (h,a)))=_
    rw [ih (fun h => pmfMean (K (n+k) h) (fun a => F (h,a)))]
    apply pmfMean_congr
    intro h
    change pmfMean (finiteContinuationLaw K n h k)
      (fun u => pmfMean (K (n+k) (finiteHistoryAppend n h k u))
        (fun a => F (finiteHistoryAppend n h k u,a)))=
      pmfMean (finiteConditionalPMF _ _) (fun u => F (finiteHistoryAppend n h (k+1) u))
    rw [finiteConditionalPMF_mean]
    rfl

end
end SecondOrder
