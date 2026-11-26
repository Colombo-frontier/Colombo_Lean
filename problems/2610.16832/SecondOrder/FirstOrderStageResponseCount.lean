import SecondOrder.CurvatureStageResponseCount
import SecondOrder.FirstOrderStageFastProbability

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

def firstOrderStageResponseCount (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (stage : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => firstOrderStageResponseCount P Θ A β z stage n+
      if firstOrderComparisonIndex P Θ A β z n=stage then 1 else 0

theorem firstOrderStageResponseCount_mono (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (stage : ℕ) :
    Monotone (firstOrderStageResponseCount P Θ A β z stage) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [firstOrderStageResponseCount]
  exact Nat.le_add_right _ _

/-- Every response is charged to at most one of the positive stages. The
output point is tested without being charged as an additional oracle call. -/
theorem firstOrderStageResponseCount_budget (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) :
    ∀ N, (∑ i : Fin T, firstOrderStageResponseCount P Θ A β z (i.val+1) N)≤N := by
  intro N
  induction N with
  | zero => simp only [firstOrderStageResponseCount, Finset.sum_const_zero, le_refl]
  | succ N ih =>
    simp only [firstOrderStageResponseCount, Finset.sum_add_distrib]
    apply Nat.add_le_add ih
    apply nat_sum_unique_indicator_le_one (fun i : Fin T => firstOrderComparisonIndex P Θ A β z N=i.val+1)
    intro i j hi hj
    apply Fin.ext
    omega

theorem firstOrderComparisonRun_restart (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (n : ℕ) : ∀ k,
    firstOrderComparisonRun P Θ A β z (n+k)=
      firstOrderRestartRun P Θ A β n (firstOrderComparisonRun P Θ A β z n).1
        (firstOrderComparisonRun P Θ A β z n).2 (fun t => z (n+t)) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    change firstOrderComparisonStep P Θ A β (n+k) (firstOrderComparisonRun P Θ A β z (n+k)) (z (n+k))=
      firstOrderComparisonStep P Θ A β (n+k)
        (firstOrderRestartRun P Θ A β n (firstOrderComparisonRun P Θ A β z n).1
          (firstOrderComparisonRun P Θ A β z n).2 (fun t => z (n+t)) k) (z (n+k))
    rw [ih]

theorem firstOrderComparisonIndex_restart (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (n k : ℕ) :
    firstOrderComparisonIndex P Θ A β z (n+k)=
      firstOrderRestartIndex P Θ A β n (firstOrderComparisonRun P Θ A β z n).1
        (firstOrderComparisonRun P Θ A β z n).2 (fun t => z (n+t)) k := by
  unfold firstOrderComparisonIndex firstOrderComparisonQuery firstOrderRestartIndex
  rw [firstOrderComparisonRun_restart P Θ A β z n k]

theorem firstOrderStageResponseCount_restart (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (stage n : ℕ) : ∀ k,
    firstOrderStageResponseCount P Θ A β z stage (n+k)=
      firstOrderStageResponseCount P Θ A β z stage n+
        firstOrderRestartCount P Θ A β n (firstOrderComparisonRun P Θ A β z n).1 stage
          (firstOrderComparisonRun P Θ A β z n).2 (fun t => z (n+t)) k := by
  intro k
  induction k with
  | zero => simp only [Nat.add_zero, firstOrderRestartCount]
  | succ k ih =>
    change firstOrderStageResponseCount P Θ A β z stage (n+k+1)=_
    rw [firstOrderStageResponseCount, firstOrderRestartCount, ih, firstOrderComparisonIndex_restart]
    omega

end
end SecondOrder
