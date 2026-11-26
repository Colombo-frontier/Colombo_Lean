import SecondOrder.FirstOrderReferenceActivation
import SecondOrder.FirstOrderComparisonUnrevealed

open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- Resample one hidden block, then run the actual adaptive comparison law. -/
def firstOrderCoordinateSamplingLaw (μ : PMF ((Fin d → Bool))) (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (i : Fin (T+1)) (n : ℕ) :=
  finiteConditionalPMF μ (fun θ => firstOrderComparisonSamplingLaw P (Function.update Θ i θ) A β R hR a₀ n)

/-- Before the first response at stage i, the new hidden vector retains its
prior distribution even after restricting to any specified entry history. -/
theorem firstOrderStageEntry_hidden_factor (μ : PMF ((Fin d → Bool))) (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (i : Fin (T+1)) (n : ℕ)
    (H : FiniteHistory Unit (FirstOrderCoefficients d T R) n → Prop) (f : (Fin d → Bool) → ℝ) :
    pmfMean (firstOrderCoordinateSamplingLaw μ P Θ A β R hR a₀ i n)
      (fun w => if firstOrderStageEntry P (Function.update Θ i w.1) A β
        (finiteHistoryTape a₀ n w.2) i.val n ∧ H w.2 then f w.1 else 0)=
    pmfMean μ f * pmfEventProbability (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ n)
      (fun h => decide (firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n ∧ H h)) := by
  let K := fun θ => firstOrderComparisonSamplingLaw P (Function.update Θ i θ) A β R hR a₀ n
  let E := fun θ h => firstOrderStageEntry P (Function.update Θ i θ) A β
    (finiteHistoryTape a₀ n h) i.val n ∧ H h
  have he (θ : (Fin d → Bool)) h : E θ h ↔ E (Θ i) h :=
    and_congr (firstOrderStageEntry_iff_prefix P _ _ A β _ i.val n
      (firstOrderHidden_update_prefix Θ i θ (Θ i))) Iff.rfl
  have hk (θ : (Fin d → Bool)) h (hh : E (Θ i) h) : K θ h=K (Θ i) h := by
    have hm := firstOrderStageEntry_mass_prefix P (Function.update Θ i θ)
      (Function.update Θ i (Θ i)) A β R hR a₀ i.val n h (firstOrderHidden_update_prefix Θ i θ (Θ i))
    rw [if_pos ((he θ h).mpr hh).1, if_pos hh.1] at hm
    exact hm
  have hf := finiteHiddenSlice_factor μ K (Θ i) E f he hk
  simp only [K, E, Function.update_eq_self] at hf
  refine Eq.trans ?_ hf
  apply pmfMean_congr
  intro w
  by_cases hh : firstOrderStageEntry P (Function.update Θ i w.1) A β
      (finiteHistoryTape a₀ n w.2) i.val n ∧ H w.2
  · simp only [if_pos hh]
  · simp only [if_neg hh]

/-- One query cannot activate an unrevealed block with probability above the
original independent-sign tail, despite the adaptive history and sampling law. -/
theorem firstOrderComparison_far_coordinate (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (a₀ : FirstOrderCoefficients d T R) (i : Fin (T+1)) (n : ℕ) :
    pmfEventProbability
      (firstOrderCoordinateSamplingLaw (PMF.uniformOfFintype ((Fin d → Bool))) P Θ A β R hR a₀ i n)
      (fun w => decide ((firstOrderComparisonRun P (Function.update Θ i w.1) A β
          (finiteHistoryTape a₀ n w.2) n).1+1 ≤ i.val ∧
        0<firstOrderBlockCompletion w.1 (firstOrderDilation d T β
          (firstOrderComparisonQuery P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ n w.2) n) i)))≤
      2*Real.exp (-(d:ℝ)/128) := by
  classical
  let K := fun θ => firstOrderComparisonSamplingLaw P (Function.update Θ i θ) A β R hR a₀ n
  let E := fun θ (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) => (firstOrderComparisonRun P (Function.update Θ i θ) A β
    (finiteHistoryTape a₀ n h) n).1+1 ≤ i.val
  let F := fun θ (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) => 0<firstOrderBlockCompletion θ (firstOrderDilation d T β
    (firstOrderComparisonQuery P (Function.update Θ i θ) A β (finiteHistoryTape a₀ n h) n) i)
  have he (θ : (Fin d → Bool)) h : E θ h ↔ E (Θ i) h :=
    firstOrderUnrevealed_iff_prefix P _ _ A β _ i.val n (firstOrderHidden_update_prefix Θ i θ (Θ i))
  have hk (θ : (Fin d → Bool)) h (hh : E (Θ i) h) : K θ h=K (Θ i) h :=
    firstOrderUnrevealed_mass_prefix P _ _ A β R hR a₀ i.val n h
      (firstOrderHidden_update_prefix Θ i θ (Θ i)) ((he θ h).mpr hh)
  have hf h (hh : E (Θ i) h) :
      pmfEventProbability (PMF.uniformOfFintype ((Fin d → Bool))) (fun θ => decide (F θ h))≤
        2*Real.exp (-(d:ℝ)/128) := by
    have hq (θ : (Fin d → Bool)) : firstOrderComparisonQuery P (Function.update Θ i θ) A β
        (finiteHistoryTape a₀ n h) n=firstOrderComparisonQuery P (Function.update Θ i (Θ i)) A β
          (finiteHistoryTape a₀ n h) n := by
      unfold firstOrderComparisonQuery
      rw [(firstOrderUnrevealed_prefix P _ _ A β _ i.val n
        (firstOrderHidden_update_prefix Θ i θ (Θ i)) ((he θ h).mpr hh)).2]
    have heq : (fun θ => decide (F θ h))=(fun θ => decide (0<firstOrderBlockCompletion θ
        (firstOrderDilation d T β (firstOrderComparisonQuery P (Function.update Θ i (Θ i)) A β
          (finiteHistoryTape a₀ n h) n) i))) := by
      funext θ
      dsimp only [F]
      rw [hq θ]
    rw [heq]
    exact firstOrderBlockCompletion_activation_pmf _
  have hb := finiteHiddenSlice_probability_le (PMF.uniformOfFintype ((Fin d → Bool)))
    K (Θ i) E F he hk hf
  have hfinal : (2*Real.exp (-(d:ℝ)/128))*
      pmfEventProbability (K (Θ i)) (fun h => @decide (E (Θ i) h) (Classical.propDecidable _))≤2*Real.exp (-(d:ℝ)/128) := by
    have hl := pmfEventProbability_le_one (K (Θ i)) (fun h => @decide (E (Θ i) h) (Classical.propDecidable _))
    nlinarith [Real.exp_pos (-(d:ℝ)/128)]
  convert hb.trans hfinal using 1
  congr 1
  funext w
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, E, F]

end
end SecondOrder

