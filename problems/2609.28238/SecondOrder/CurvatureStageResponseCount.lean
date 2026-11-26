import SecondOrder.CurvatureStageFastProbability

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

theorem nat_sum_unique_indicator_le_one {I : Type*} [Fintype I] (E : I → Prop) [DecidablePred E]
    (hunique : ∀ i j, E i → E j → i=j) : (∑ i, if E i then (1:ℕ) else 0)≤1 := by
  by_cases he : ∃ i, E i
  · obtain ⟨i,hi⟩ := he
    rw [Finset.sum_eq_single i]
    · simp only [if_pos hi, le_refl]
    · intro j _ hji
      exact if_neg (fun hj => hji (hunique j i hj hi))
    · simp
  · have hn : ∀ i, ¬E i := by simpa only [not_exists] using he
    simp only [if_neg (hn _), Finset.sum_const_zero, zero_le_one]

variable {m T : ℕ} {S : Type*}

def curvatureStageResponseCount (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (stage : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => curvatureStageResponseCount P Θ A β z stage n+
      if curvatureComparisonIndex P Θ A β z n=stage then 1 else 0

theorem curvatureStageResponseCount_mono (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (stage : ℕ) :
    Monotone (curvatureStageResponseCount P Θ A β z stage) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [curvatureStageResponseCount]
  exact Nat.le_add_right _ _

/-- Every response is charged to at most one of the positive stages. The
output point is tested without being charged as an additional oracle call. -/
theorem curvatureStageResponseCount_budget (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) :
    ∀ N, (∑ i : Fin T, curvatureStageResponseCount P Θ A β z (i.val+1) N)≤N := by
  intro N
  induction N with
  | zero => simp only [curvatureStageResponseCount, Finset.sum_const_zero, le_refl]
  | succ N ih =>
    simp only [curvatureStageResponseCount, Finset.sum_add_distrib]
    apply Nat.add_le_add ih
    apply nat_sum_unique_indicator_le_one (fun i : Fin T => curvatureComparisonIndex P Θ A β z N=i.val+1)
    intro i j hi hj
    apply Fin.ext
    omega

theorem curvatureComparisonRun_restart (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (n : ℕ) : ∀ k,
    curvatureComparisonRun P Θ A β z (n+k)=
      curvatureRestartRun P Θ A β n (curvatureComparisonRun P Θ A β z n).1
        (curvatureComparisonRun P Θ A β z n).2 (fun t => z (n+t)) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    change curvatureComparisonStep P Θ A β (n+k) (curvatureComparisonRun P Θ A β z (n+k)) (z (n+k))=
      curvatureComparisonStep P Θ A β (n+k)
        (curvatureRestartRun P Θ A β n (curvatureComparisonRun P Θ A β z n).1
          (curvatureComparisonRun P Θ A β z n).2 (fun t => z (n+t)) k) (z (n+k))
    rw [ih]

theorem curvatureComparisonIndex_restart (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (n k : ℕ) :
    curvatureComparisonIndex P Θ A β z (n+k)=
      curvatureRestartIndex P Θ A β n (curvatureComparisonRun P Θ A β z n).1
        (curvatureComparisonRun P Θ A β z n).2 (fun t => z (n+t)) k := by
  unfold curvatureComparisonIndex curvatureComparisonQuery curvatureRestartIndex
  rw [curvatureComparisonRun_restart P Θ A β z n k]

theorem curvatureStageResponseCount_restart (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (stage n : ℕ) : ∀ k,
    curvatureStageResponseCount P Θ A β z stage (n+k)=
      curvatureStageResponseCount P Θ A β z stage n+
        curvatureRestartCount P Θ A β n (curvatureComparisonRun P Θ A β z n).1 stage
          (curvatureComparisonRun P Θ A β z n).2 (fun t => z (n+t)) k := by
  intro k
  induction k with
  | zero => simp only [Nat.add_zero, curvatureRestartCount]
  | succ k ih =>
    change curvatureStageResponseCount P Θ A β z stage (n+k+1)=_
    rw [curvatureStageResponseCount, curvatureRestartCount, ih, curvatureComparisonIndex_restart]
    omega

end
end SecondOrder
