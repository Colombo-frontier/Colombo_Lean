import SecondOrder.FirstOrderResponseTransport

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

def firstOrderStateFar (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (β : ℝ) (n : ℕ) (s : ℕ × S) : Prop :=
  ∃ i, s.1+1 ≤ i.val ∧ 0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β (P.query n s.2) i)

def firstOrderObservedInitial (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool)) (β : ℝ) :
    Prop × (ℕ × S) := (firstOrderStateFar P Θ β 0 (0,P.initial),(0,P.initial))

/-- Keep the complete current state and the event that a far jump has occurred,
including the next query point. The event is only a deterministic observer. -/
def firstOrderObservedStep (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (n : ℕ) (s : Prop × (ℕ × S)) (z : FirstOrderCoefficients d T R) :
    Prop × (ℕ × S) :=
  let s' := firstOrderComparisonStep P Θ A β n s.2 z
  (s.1 ∨ firstOrderStateFar P Θ β (n+1) s',s')

def firstOrderObservedPrefix (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (β R : ℝ) (hR : 2≤R) (n : ℕ) (s : Prop × (ℕ × S)) : PMF (FirstOrderCoefficients d T R) :=
  firstOrderPrefixCoefficientLaw Θ R hR (firstOrderLimitedProgress Θ β (P.query n s.2.2) (s.2.1+1)+1)

theorem firstOrderComparisonRun_history_succ (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) (n+1)) :
    firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ (n+1) h) (n+1)=
      firstOrderComparisonStep P Θ A β n (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h.1) n) h.2 := by
  rw [firstOrderComparisonRun, finiteHistoryTape_succ_at,
    firstOrderComparisonRun_tape_congr P Θ A β _ _ n (finiteHistoryTape_succ_lt a₀ n h)]

theorem firstOrderObservedRun_eq (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (a₀ : FirstOrderCoefficients d T R) : ∀ n h,
    finiteStateRun (firstOrderObservedInitial P Θ β) (firstOrderObservedStep P Θ A β) n h=
      (firstOrderHistoryFar P Θ A β a₀ n h,firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n) := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    rw [finiteStateRun, ih]
    apply Prod.ext
    · apply propext
      change (_ ∨ _) ↔ (_ ∨ _)
      apply or_congr Iff.rfl
      change firstOrderStateFar P Θ β (n+1)
        (firstOrderComparisonStep P Θ A β n (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h.1) n) h.2) ↔
          firstOrderStateFar P Θ β (n+1) (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ (n+1) h) (n+1))
      rw [firstOrderComparisonRun_history_succ]
    · exact (firstOrderComparisonRun_history_succ P Θ A β a₀ n h).symm

theorem firstOrderObservedStep_mean_transport (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (n : ℕ) (s : Prop × (ℕ × S)) (F : (Prop × (ℕ × S)) → ℝ) :
    pmfMean (firstOrderChainCoefficientLaw Θ R hR) (fun z => F (firstOrderObservedStep P Θ A β n s z))=
      pmfMean (firstOrderObservedPrefix P Θ β R hR n s) (fun z => F (firstOrderObservedStep P Θ A β n s z)) :=
  firstOrderComparisonStep_mean_transport P Θ A β R hR n s.2
    (fun s' => F (s.1 ∨ firstOrderStateFar P Θ β (n+1) s',s'))

end
end SecondOrder

