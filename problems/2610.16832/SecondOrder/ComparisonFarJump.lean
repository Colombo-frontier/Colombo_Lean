import SecondOrder.FiniteCoordinateResampling

open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

def curvatureHiddenPrior (m T : ℕ) : PMF (Fin (T+1) → BalancedVector m) :=
  finitePiPMF (fun _ => PMF.uniformOfFintype (BalancedVector m))

def curvatureComparisonJointLaw (P : CurvaturePolicy m T S) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) :=
  finiteConditionalPMF (curvatureHiddenPrior m T)
    (fun Θ => curvatureComparisonSamplingLaw P Θ A β R hR a₀ n)

def curvatureFarAt (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (n : ℕ) (i : Fin (T+1)) : Prop :=
  (curvatureComparisonRun P Θ A β z n).1+1 ≤ i.val ∧
    0<periodicCompletion (Θ i) (curvatureDilation m T β (curvatureComparisonQuery P Θ A β z n) i)

theorem curvatureFarAt_tape_congr (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z z' : ℕ → CurvatureCoefficients m T R) (n : ℕ)
    (hz : ∀ t, t<n → z t=z' t) (i : Fin (T+1)) :
    curvatureFarAt P Θ A β z n i ↔ curvatureFarAt P Θ A β z' n i := by
  unfold curvatureFarAt curvatureComparisonQuery
  rw [curvatureComparisonRun_tape_congr P Θ A β z z' n hz]

/-- Average over all hidden blocks, preserving the actual adaptive history
law. Each single unrevealed block still has the same activation tail. -/
theorem curvatureComparison_far_at (P : CurvaturePolicy m T S) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) (i : Fin (T+1)) :
    pmfEventProbability (curvatureComparisonJointLaw P A β R hR a₀ n)
      (fun w => decide (curvatureFarAt P w.1 A β (finiteHistoryTape a₀ n w.2) n i))≤
      4*Real.exp (-((2*m:ℕ):ℝ)/512) := by
  rw [pmfEventProbability_mean, curvatureComparisonJointLaw, finiteConditionalPMF_mean]
  simp only [decide_eq_true_eq]
  let G := fun Θ => pmfMean (curvatureComparisonSamplingLaw P Θ A β R hR a₀ n)
    (fun h => if curvatureFarAt P Θ A β (finiteHistoryTape a₀ n h) n i then (1:ℝ) else 0)
  unfold curvatureHiddenPrior
  change pmfMean (finitePiPMF (fun _ : Fin (T+1) => PMF.uniformOfFintype (BalancedVector m))) G≤_
  have he := finitePiPMF_resample_mean_any_fintype inferInstance
    (fun _ : Fin (T+1) => PMF.uniformOfFintype (BalancedVector m)) i G
  rw [←he]
  apply pmfMean_le_const
  intro Θ
  have hh := curvatureComparison_far_coordinate P Θ A β R hR a₀ i n
  rw [pmfEventProbability_mean, curvatureCoordinateSamplingLaw, finiteConditionalPMF_mean] at hh
  simpa only [G, curvatureFarAt, Function.update_self, decide_eq_true_eq] using hh

/-- The entire collection of future blocks at one adaptive query. -/
theorem curvatureComparison_far_any_at (P : CurvaturePolicy m T S) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (n : ℕ) :
    pmfEventProbability (curvatureComparisonJointLaw P A β R hR a₀ n)
      (fun w => decide (∃ i, curvatureFarAt P w.1 A β (finiteHistoryTape a₀ n w.2) n i))≤
      (T+1:ℕ)*(4*Real.exp (-((2*m:ℕ):ℝ)/512)) := by
  have hu := pmfEventProbability_union (curvatureComparisonJointLaw P A β R hR a₀ n)
    (fun i w => decide (curvatureFarAt P w.1 A β (finiteHistoryTape a₀ n w.2) n i))
  simp only [decide_eq_true_eq] at hu
  apply hu.trans
  calc
    _ ≤ ∑ _i : Fin (T+1), 4*Real.exp (-((2*m:ℕ):ℝ)/512) :=
      Finset.sum_le_sum (fun i _ => curvatureComparison_far_at P A β R hR a₀ n i)
    _ = _ := by simp

end
end SecondOrder
