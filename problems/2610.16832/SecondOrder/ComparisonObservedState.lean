import SecondOrder.CurvatureResponseTransport

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

def curvatureStateFar (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (β : ℝ) (n : ℕ) (s : ℕ × S) : Prop :=
  ∃ i, s.1+1 ≤ i.val ∧ 0<periodicCompletion (Θ i) (curvatureDilation m T β (P.query n s.2) i)

def curvatureObservedInitial (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m) (β : ℝ) :
    Prop × (ℕ × S) := (curvatureStateFar P Θ β 0 (0,P.initial),(0,P.initial))

/-- Keep the complete current state and the event that a far jump has occurred,
including the next query point. The event is only a deterministic observer. -/
def curvatureObservedStep (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (n : ℕ) (s : Prop × (ℕ × S)) (z : CurvatureCoefficients m T R) :
    Prop × (ℕ × S) :=
  let s' := curvatureComparisonStep P Θ A β n s.2 z
  (s.1 ∨ curvatureStateFar P Θ β (n+1) s',s')

def curvatureObservedPrefix (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (β R : ℝ) (hR : 2≤R) (n : ℕ) (s : Prop × (ℕ × S)) : PMF (CurvatureCoefficients m T R) :=
  curvaturePrefixCoefficientLaw Θ R hR (curvatureLimitedProgress Θ β (P.query n s.2.2) (s.2.1+1)+1)

theorem curvatureComparisonRun_history_succ (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) (n+1)) :
    curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ (n+1) h) (n+1)=
      curvatureComparisonStep P Θ A β n (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h.1) n) h.2 := by
  rw [curvatureComparisonRun, finiteHistoryTape_succ_at,
    curvatureComparisonRun_tape_congr P Θ A β _ _ n (finiteHistoryTape_succ_lt a₀ n h)]

theorem curvatureObservedRun_eq (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (a₀ : CurvatureCoefficients m T R) : ∀ n h,
    finiteStateRun (curvatureObservedInitial P Θ β) (curvatureObservedStep P Θ A β) n h=
      (curvatureHistoryFar P Θ A β a₀ n h,curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n) := by
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
      change curvatureStateFar P Θ β (n+1)
        (curvatureComparisonStep P Θ A β n (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h.1) n) h.2) ↔
          curvatureStateFar P Θ β (n+1) (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ (n+1) h) (n+1))
      rw [curvatureComparisonRun_history_succ]
    · exact (curvatureComparisonRun_history_succ P Θ A β a₀ n h).symm

theorem curvatureObservedStep_mean_transport (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (n : ℕ) (s : Prop × (ℕ × S)) (F : (Prop × (ℕ × S)) → ℝ) :
    pmfMean (curvatureCoefficientLaw Θ R hR) (fun z => F (curvatureObservedStep P Θ A β n s z))=
      pmfMean (curvatureObservedPrefix P Θ β R hR n s) (fun z => F (curvatureObservedStep P Θ A β n s z)) :=
  curvatureComparisonStep_mean_transport P Θ A β R hR n s.2
    (fun s' => F (s.1 ∨ curvatureStateFar P Θ β (n+1) s',s'))

end
end SecondOrder
