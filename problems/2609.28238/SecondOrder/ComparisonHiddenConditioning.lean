import SecondOrder.ComparisonUnrevealed

open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

/-- Resample one hidden block, then run the actual adaptive comparison law. -/
def curvatureCoordinateSamplingLaw (μ : PMF (BalancedVector m)) (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (i : Fin (T+1)) (n : ℕ) :=
  finiteConditionalPMF μ (fun θ => curvatureComparisonSamplingLaw P (Function.update Θ i θ) A β R hR a₀ n)

/-- Before the first response at stage i, the new hidden vector retains its
prior distribution even after restricting to any specified entry history. -/
theorem curvatureStageEntry_hidden_factor (μ : PMF (BalancedVector m)) (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (i : Fin (T+1)) (n : ℕ)
    (H : FiniteHistory Unit (CurvatureCoefficients m T R) n → Prop) (f : BalancedVector m → ℝ) :
    pmfMean (curvatureCoordinateSamplingLaw μ P Θ A β R hR a₀ i n)
      (fun w => if curvatureStageEntry P (Function.update Θ i w.1) A β
        (finiteHistoryTape a₀ n w.2) i.val n ∧ H w.2 then f w.1 else 0)=
    pmfMean μ f * pmfEventProbability (curvatureComparisonSamplingLaw P Θ A β R hR a₀ n)
      (fun h => decide (curvatureStageEntry P Θ A β (finiteHistoryTape a₀ n h) i.val n ∧ H h)) := by
  let K := fun θ => curvatureComparisonSamplingLaw P (Function.update Θ i θ) A β R hR a₀ n
  let E := fun θ h => curvatureStageEntry P (Function.update Θ i θ) A β
    (finiteHistoryTape a₀ n h) i.val n ∧ H h
  have he (θ : BalancedVector m) h : E θ h ↔ E (Θ i) h :=
    and_congr (curvatureStageEntry_iff_prefix P _ _ A β _ i.val n
      (curvatureHidden_update_prefix Θ i θ (Θ i))) Iff.rfl
  have hk (θ : BalancedVector m) h (hh : E (Θ i) h) : K θ h=K (Θ i) h := by
    have hm := curvatureStageEntry_mass_prefix P (Function.update Θ i θ)
      (Function.update Θ i (Θ i)) A β R hR a₀ i.val n h (curvatureHidden_update_prefix Θ i θ (Θ i))
    rw [if_pos ((he θ h).mpr hh).1, if_pos hh.1] at hm
    exact hm
  have hf := finiteHiddenSlice_factor μ K (Θ i) E f he hk
  simp only [K, E, Function.update_eq_self] at hf
  refine Eq.trans ?_ hf
  apply pmfMean_congr
  intro w
  by_cases hh : curvatureStageEntry P (Function.update Θ i w.1) A β
      (finiteHistoryTape a₀ n w.2) i.val n ∧ H w.2
  · simp only [if_pos hh]
  · simp only [if_neg hh]

/-- One query cannot activate an unrevealed block with probability above the
original balanced-sign tail, despite the adaptive history and sampling law. -/
theorem curvatureComparison_far_coordinate (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (a₀ : CurvatureCoefficients m T R) (i : Fin (T+1)) (n : ℕ) :
    pmfEventProbability
      (curvatureCoordinateSamplingLaw (PMF.uniformOfFintype (BalancedVector m)) P Θ A β R hR a₀ i n)
      (fun w => decide ((curvatureComparisonRun P (Function.update Θ i w.1) A β
          (finiteHistoryTape a₀ n w.2) n).1+1 ≤ i.val ∧
        0<periodicCompletion w.1 (curvatureDilation m T β
          (curvatureComparisonQuery P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ n w.2) n) i)))≤
      4*Real.exp (-((2*m:ℕ):ℝ)/512) := by
  classical
  let K := fun θ => curvatureComparisonSamplingLaw P (Function.update Θ i θ) A β R hR a₀ n
  let E := fun θ (h : FiniteHistory Unit (CurvatureCoefficients m T R) n) => (curvatureComparisonRun P (Function.update Θ i θ) A β
    (finiteHistoryTape a₀ n h) n).1+1 ≤ i.val
  let F := fun θ (h : FiniteHistory Unit (CurvatureCoefficients m T R) n) => 0<periodicCompletion θ (curvatureDilation m T β
    (curvatureComparisonQuery P (Function.update Θ i θ) A β (finiteHistoryTape a₀ n h) n) i)
  have he (θ : BalancedVector m) h : E θ h ↔ E (Θ i) h :=
    curvatureUnrevealed_iff_prefix P _ _ A β _ i.val n (curvatureHidden_update_prefix Θ i θ (Θ i))
  have hk (θ : BalancedVector m) h (hh : E (Θ i) h) : K θ h=K (Θ i) h :=
    curvatureUnrevealed_mass_prefix P _ _ A β R hR a₀ i.val n h
      (curvatureHidden_update_prefix Θ i θ (Θ i)) ((he θ h).mpr hh)
  have hf h (hh : E (Θ i) h) :
      pmfEventProbability (PMF.uniformOfFintype (BalancedVector m)) (fun θ => decide (F θ h))≤
        4*Real.exp (-((2*m:ℕ):ℝ)/512) := by
    have hq (θ : BalancedVector m) : curvatureComparisonQuery P (Function.update Θ i θ) A β
        (finiteHistoryTape a₀ n h) n=curvatureComparisonQuery P (Function.update Θ i (Θ i)) A β
          (finiteHistoryTape a₀ n h) n := by
      unfold curvatureComparisonQuery
      rw [(curvatureUnrevealed_prefix P _ _ A β _ i.val n
        (curvatureHidden_update_prefix Θ i θ (Θ i)) ((he θ h).mpr hh)).2]
    have heq : (fun θ => decide (F θ h))=(fun θ => decide (0<periodicCompletion θ
        (curvatureDilation m T β (curvatureComparisonQuery P (Function.update Θ i (Θ i)) A β
          (finiteHistoryTape a₀ n h) n) i))) := by
      funext θ
      dsimp only [F]
      rw [hq θ]
    rw [heq]
    exact periodicCompletion_activation_pmf _
  have hb := finiteHiddenSlice_probability_le (PMF.uniformOfFintype (BalancedVector m))
    K (Θ i) E F he hk hf
  have hfinal : (4*Real.exp (-((2*m:ℕ):ℝ)/512))*
      pmfEventProbability (K (Θ i)) (fun h => @decide (E (Θ i) h) (Classical.propDecidable _))≤4*Real.exp (-((2*m:ℕ):ℝ)/512) := by
    have hl := pmfEventProbability_le_one (K (Θ i)) (fun h => @decide (E (Θ i) h) (Classical.propDecidable _))
    nlinarith [Real.exp_pos (-((2*m:ℕ):ℝ)/512)]
  convert hb.trans hfinal using 1
  congr 1
  funext w
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, E, F]

end
end SecondOrder
