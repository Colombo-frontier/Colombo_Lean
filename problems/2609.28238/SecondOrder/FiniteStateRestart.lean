import SecondOrder.FiniteConditionalContinuation

open scoped Classical

namespace SecondOrder
noncomputable section
variable {A : Type} {B : Type*}

theorem stateTapeRun_restart (b₀ : B) (U : ℕ → B → A → B) (z : ℕ → A) (n : ℕ) :
    ∀ k, stateTapeRun b₀ U z (n+k)=
      stateTapeRun (stateTapeRun b₀ U z n) (fun t => U (n+t)) (fun t => z (n+t)) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    change U (n+k) (stateTapeRun b₀ U z (n+k)) (z (n+k))=
      U (n+k) (stateTapeRun (stateTapeRun b₀ U z n) (fun t => U (n+t)) (fun t => z (n+t)) k) (z (n+k))
    rw [ih]

theorem finiteStateRun_append [Fintype A] (b₀ : B) (U : ℕ → B → A → B)
    (n : ℕ) (h : FiniteHistory Unit A n) : ∀ k u,
    finiteStateRun b₀ U (n+k) (finiteHistoryAppend n h k u)=
      finiteStateRun (finiteStateRun b₀ U n h) (fun t => U (n+t)) k u := by
  intro k
  induction k with
  | zero => intro u; rfl
  | succ k ih =>
    intro u
    change U (n+k) (finiteStateRun b₀ U (n+k) (finiteHistoryAppend n h k u.1)) u.2=
      U (n+k) (finiteStateRun (finiteStateRun b₀ U n h) (fun t => U (n+t)) k u.1) u.2
    rw [ih]

variable {m T : ℕ} {S : Type*}

theorem curvatureComparisonRun_finite (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (a₀ : CurvatureCoefficients m T R) : ∀ n h,
    curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n=
      finiteStateRun (0,P.initial) (curvatureComparisonStep P Θ A β) n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    rw [curvatureComparisonRun_history_succ, finiteStateRun, ih]

theorem curvatureComparisonRun_append (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) n)
    (k : ℕ) (u : FiniteHistory Unit (CurvatureCoefficients m T R) k) :
    curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ (n+k) (finiteHistoryAppend n h k u)) (n+k)=
      curvatureRestartRun P Θ A β n (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1
        (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 (finiteHistoryTape a₀ k u) k := by
  rw [curvatureComparisonRun_finite, finiteStateRun_append,
    curvatureComparisonRun_finite P Θ A β a₀ n h]
  exact finiteStateRun_eq_tape _ _ a₀ k u

theorem curvatureComparisonIndex_append (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) n)
    (k : ℕ) (u : FiniteHistory Unit (CurvatureCoefficients m T R) k) :
    curvatureComparisonIndex P Θ A β (finiteHistoryTape a₀ (n+k) (finiteHistoryAppend n h k u)) (n+k)=
      curvatureRestartIndex P Θ A β n (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1
        (curvatureComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 (finiteHistoryTape a₀ k u) k := by
  unfold curvatureComparisonIndex curvatureComparisonQuery curvatureRestartIndex
  rw [curvatureComparisonRun_append]

end
end SecondOrder
