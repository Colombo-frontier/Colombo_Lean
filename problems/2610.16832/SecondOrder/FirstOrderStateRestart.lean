import SecondOrder.FiniteStateRestart
import SecondOrder.FirstOrderContinuationCoupling
import SecondOrder.FiniteConditionalContinuation

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderComparisonRun_finite (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (a₀ : FirstOrderCoefficients d T R) : ∀ n h,
    firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n=
      finiteStateRun (0,P.initial) (firstOrderComparisonStep P Θ A β) n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    rw [firstOrderComparisonRun_history_succ, finiteStateRun, ih]

theorem firstOrderComparisonRun_append (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n)
    (k : ℕ) (u : FiniteHistory Unit (FirstOrderCoefficients d T R) k) :
    firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ (n+k) (finiteHistoryAppend n h k u)) (n+k)=
      firstOrderRestartRun P Θ A β n (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1
        (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 (finiteHistoryTape a₀ k u) k := by
  rw [firstOrderComparisonRun_finite, finiteStateRun_append,
    firstOrderComparisonRun_finite P Θ A β a₀ n h]
  exact finiteStateRun_eq_tape _ _ a₀ k u

theorem firstOrderComparisonIndex_append (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n)
    (k : ℕ) (u : FiniteHistory Unit (FirstOrderCoefficients d T R) k) :
    firstOrderComparisonIndex P Θ A β (finiteHistoryTape a₀ (n+k) (finiteHistoryAppend n h k u)) (n+k)=
      firstOrderRestartIndex P Θ A β n (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).1
        (firstOrderComparisonRun P Θ A β (finiteHistoryTape a₀ n h) n).2 (finiteHistoryTape a₀ k u) k := by
  unfold firstOrderComparisonIndex firstOrderComparisonQuery firstOrderRestartIndex
  rw [firstOrderComparisonRun_append]

end
end SecondOrder
