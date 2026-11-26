import SecondOrder.CurvatureEntryTapeEvent

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

theorem pmfEventProbability_disjoint_sum_le_one {Ω I : Type*} [Fintype Ω] [Fintype I]
    (p : PMF Ω) (E : I → Ω → Prop) (hunique : ∀ i j ω, E i ω → E j ω → i=j) :
    (∑ i, pmfEventProbability p (fun ω => decide (E i ω)))≤1 := by
  simp only [pmfEventProbability_mean, decide_eq_true_eq]
  rw [←pmfMean_finset_sum]
  apply pmfMean_le_const
  intro ω
  by_cases he : ∃ i, E i ω
  · obtain ⟨i,hi⟩ := he
    rw [Finset.sum_eq_single i]
    · simp only [if_pos hi, le_refl]
    · intro j _ hji
      exact if_neg (fun hj => hji (hunique j i ω hj hi))
    · simp
  · have hn : ∀ i, ¬E i ω := by simpa only [not_exists] using he
    simp only [if_neg (hn _), Finset.sum_const_zero, zero_le_one]

variable {m T : ℕ} {S : Type*}

theorem curvatureStageEntry_fast_tape_probability (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m) (A β R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (CurvatureDimension m T))
    (a₀ : CurvatureCoefficients m T R) (n k : ℕ)
    (hhorizon : 1024*Real.log (4*(k+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536) :
    pmfEventProbability (curvatureCoordinateSamplingLaw (PMF.uniformOfFintype (BalancedVector m))
      P Θ A β R hR a₀ i (n+k))
      (fun w => decide (curvatureStageEntry P (Function.update Θ i w.1) A β
        (finiteHistoryTape a₀ (n+k) w.2) i.val n ∧
        curvatureFastAfterEntry P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ (n+k) w.2) i cap n k))≤
      (1/32)*pmfEventProbability (curvatureComparisonSamplingLaw P Θ A β R hR a₀ (n+k))
        (fun h => decide (curvatureStageEntry P Θ A β (finiteHistoryTape a₀ (n+k) h) i.val n)) := by
  have hh := curvatureStageEntry_fast_probability P Θ hm A β R hR i cap dummy a₀ n k hhorizon hlarge hcap
  have he (Θ' : Fin (T+1) → BalancedVector m) (h : FiniteHistory Unit (CurvatureCoefficients m T R) (n+k)) :=
    curvatureStageEntry_tape_congr P Θ' A β _ _ i.val n (finiteHistoryTape_prefix a₀ n k h)
  simp_rw [he, curvatureEntryFutureFast_tape] at hh
  rw [curvatureStageEntry_prefix_probability]
  exact hh

def curvatureStageFast (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (i : Fin (T+1)) (cap N : ℕ) : Prop :=
  ∃ n : Fin (N+1), curvatureStageEntry P Θ A β z i.val n.val ∧
    curvatureFastAfterEntry P Θ A β z i cap n.val (N-n.val)

/-- Summing entry times costs no factor of the horizon: all entrance events
of a fixed stage are disjoint under the same full-history probability law. -/
theorem curvatureStageFast_coordinate_probability (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m) (A β R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (CurvatureDimension m T))
    (a₀ : CurvatureCoefficients m T R) (N : ℕ)
    (hhorizon : 1024*Real.log (4*(N+1:ℕ))≤((2*m:ℕ):ℝ))
    (hlarge : 65536*Real.log 2≤((2*m:ℕ):ℝ))
    (hcap : curvatureArrayInformation m R*cap≤((2*m:ℕ):ℝ)/65536) :
    pmfEventProbability (curvatureCoordinateSamplingLaw (PMF.uniformOfFintype (BalancedVector m))
      P Θ A β R hR a₀ i N)
      (fun w => decide (curvatureStageFast P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ N w.2) i cap N))≤1/32 := by
  have htime (n : ℕ) (hn : n≤N) :
      pmfEventProbability (curvatureCoordinateSamplingLaw (PMF.uniformOfFintype (BalancedVector m))
        P Θ A β R hR a₀ i N)
        (fun w => decide (curvatureStageEntry P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ N w.2) i.val n ∧
          curvatureFastAfterEntry P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ N w.2) i cap n (N-n)))≤
        (1/32)*pmfEventProbability (curvatureComparisonSamplingLaw P Θ A β R hR a₀ N)
          (fun h => decide (curvatureStageEntry P Θ A β (finiteHistoryTape a₀ N h) i.val n)) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
    have hh : 1024*Real.log (4*(k+1:ℕ))≤((2*m:ℕ):ℝ) := by
      apply le_trans _ hhorizon
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.log_le_log (by positivity)
      have hkN : k≤N := by omega
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.succ_le_succ hkN) (by norm_num)
    subst N
    simpa only [Nat.add_sub_cancel_left] using
      curvatureStageEntry_fast_tape_probability P Θ hm A β R hR i cap dummy a₀ n k hh hlarge hcap
  have hu := pmfEventProbability_union
    (curvatureCoordinateSamplingLaw (PMF.uniformOfFintype (BalancedVector m)) P Θ A β R hR a₀ i N)
    (fun n : Fin (N+1) => fun w => decide
      (curvatureStageEntry P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ N w.2) i.val n.val ∧
        curvatureFastAfterEntry P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ N w.2) i cap n.val (N-n.val)))
  simp only [decide_eq_true_eq] at hu
  have hsum := Finset.sum_le_sum (fun (n : Fin (N+1)) (_ : n ∈ Finset.univ) => htime n.val (by omega))
  have htrans := hu.trans hsum
  suffices (1/32)*(∑ n : Fin (N+1), pmfEventProbability (curvatureComparisonSamplingLaw P Θ A β R hR a₀ N)
      (fun h => decide (curvatureStageEntry P Θ A β (finiteHistoryTape a₀ N h) i.val n.val)))≤1/32 by
    rw [←Finset.mul_sum] at htrans
    simpa only [curvatureStageFast, pmfEventProbability_mean, decide_eq_true_eq] using htrans.trans this
  have hs := pmfEventProbability_disjoint_sum_le_one (curvatureComparisonSamplingLaw P Θ A β R hR a₀ N)
    (fun n : Fin (N+1) => fun h => curvatureStageEntry P Θ A β (finiteHistoryTape a₀ N h) i.val n.val)
    (fun n k h hn hk => Fin.ext (curvatureStageEntry_unique P Θ A β _ hn hk))
  linarith only [hs]

end
end SecondOrder
