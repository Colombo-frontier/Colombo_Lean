import SecondOrder.FirstOrderComparisonHiddenConditioning
import SecondOrder.FiniteCoordinateResampling

open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

def firstOrderHiddenPrior (d T : ℕ) : PMF (Fin (T+1) → (Fin d → Bool)) :=
  finitePiPMF (fun _ => PMF.uniformOfFintype ((Fin d → Bool)))

def firstOrderComparisonJointLaw (P : FirstOrderPolicy d T S) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) :=
  finiteConditionalPMF (firstOrderHiddenPrior d T)
    (fun Θ => firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n)

def firstOrderFarAt (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (n : ℕ) (i : Fin (T+1)) : Prop :=
  (firstOrderComparisonRun P Θ A β z n).1+1 ≤ i.val ∧
    0<firstOrderBlockCompletion (Θ i) (firstOrderDilation d T β (firstOrderComparisonQuery P Θ A β z n) i)

theorem firstOrderFarAt_tape_congr (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z z' : ℕ → FirstOrderCoefficients d T R) (n : ℕ)
    (hz : ∀ t, t<n → z t=z' t) (i : Fin (T+1)) :
    firstOrderFarAt P Θ A β z n i ↔ firstOrderFarAt P Θ A β z' n i := by
  unfold firstOrderFarAt firstOrderComparisonQuery
  rw [firstOrderComparisonRun_tape_congr P Θ A β z z' n hz]

/-- Average over all hidden blocks, preserving the actual adaptive history
law. Each single unrevealed block still has the same activation tail. -/
theorem firstOrderComparison_far_at (P : FirstOrderPolicy d T S) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) (i : Fin (T+1)) :
    pmfEventProbability (firstOrderComparisonJointLaw P A β R hR a₀ n)
      (fun w => decide (firstOrderFarAt P w.1 A β (finiteHistoryTape a₀ n w.2) n i))≤
      2*Real.exp (-(d:ℝ)/128) := by
  rw [pmfEventProbability_mean, firstOrderComparisonJointLaw, finiteConditionalPMF_mean]
  simp only [decide_eq_true_eq]
  let G := fun Θ => pmfMean (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n)
    (fun h => if firstOrderFarAt P Θ A β (finiteHistoryTape a₀ n h) n i then (1:ℝ) else 0)
  unfold firstOrderHiddenPrior
  change pmfMean (finitePiPMF (fun _ : Fin (T+1) => PMF.uniformOfFintype ((Fin d → Bool)))) G≤_
  have he := finitePiPMF_resample_mean_any_fintype inferInstance
    (fun _ : Fin (T+1) => PMF.uniformOfFintype ((Fin d → Bool))) i G
  rw [←he]
  apply pmfMean_le_const
  intro Θ
  have hh := firstOrderComparison_far_coordinate P Θ A β R hR a₀ i n
  rw [pmfEventProbability_mean, firstOrderCoordinateSamplingLaw, finiteConditionalPMF_mean] at hh
  simpa only [G, firstOrderFarAt, Function.update_self, decide_eq_true_eq] using hh

/-- The entire collection of future blocks at one adaptive query. -/
theorem firstOrderComparison_far_any_at (P : FirstOrderPolicy d T S) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (n : ℕ) :
    pmfEventProbability (firstOrderComparisonJointLaw P A β R hR a₀ n)
      (fun w => decide (∃ i, firstOrderFarAt P w.1 A β (finiteHistoryTape a₀ n w.2) n i))≤
      (T+1:ℕ)*(2*Real.exp (-(d:ℝ)/128)) := by
  have hu := pmfEventProbability_union (firstOrderComparisonJointLaw P A β R hR a₀ n)
    (fun i w => decide (firstOrderFarAt P w.1 A β (finiteHistoryTape a₀ n w.2) n i))
  simp only [decide_eq_true_eq] at hu
  apply hu.trans
  calc
    _ ≤ ∑ _i : Fin (T+1), 2*Real.exp (-(d:ℝ)/128) :=
      Finset.sum_le_sum (fun i _ => firstOrderComparison_far_at P A β R hR a₀ n i)
    _ = _ := by simp

end
end SecondOrder

