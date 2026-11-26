import SecondOrder.CurvatureEntrySum
import SecondOrder.FirstOrderEntryTapeEvent

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

theorem firstOrderStageEntry_fast_tape_probability (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (hd : 0<d) (A β R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (a₀ : FirstOrderCoefficients d T R) (n k : ℕ)
    (hhorizon : 256*Real.log (2*(k+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384) :
    pmfEventProbability (firstOrderCoordinateSamplingLaw (PMF.uniformOfFintype ((Fin d → Bool)))
      P Θ A β R hR a₀ i (n+k))
      (fun w => decide (firstOrderStageEntry P (Function.update Θ i w.1) A β
        (finiteHistoryTape a₀ (n+k) w.2) i.val n ∧
        firstOrderFastAfterEntry P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ (n+k) w.2) i cap n k))≤
      (1/32)*pmfEventProbability (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ (n+k))
        (fun h => decide (firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ (n+k) h) i.val n)) := by
  have hh := firstOrderStageEntry_fast_probability P Θ hd A β R hR i cap dummy a₀ n k hhorizon hlarge hcap
  have he (Θ' : Fin (T+1) → (Fin d → Bool)) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) (n+k)) :=
    firstOrderStageEntry_tape_congr P Θ' A β _ _ i.val n (finiteHistoryTape_prefix a₀ n k h)
  simp_rw [he, firstOrderEntryFutureFast_tape] at hh
  rw [firstOrderStageEntry_prefix_probability]
  exact hh

def firstOrderStageFast (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (i : Fin (T+1)) (cap N : ℕ) : Prop :=
  ∃ n : Fin (N+1), firstOrderStageEntry P Θ A β z i.val n.val ∧
    firstOrderFastAfterEntry P Θ A β z i cap n.val (N-n.val)

/-- Summing entry times costs no factor of the horizon: all entrance events
of a fixed stage are disjoint under the same full-history probability law. -/
theorem firstOrderStageFast_coordinate_probability (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (hd : 0<d) (A β R : ℝ) (hR : 2≤R)
    (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (a₀ : FirstOrderCoefficients d T R) (N : ℕ)
    (hhorizon : 256*Real.log (2*(N+1:ℕ))≤(d:ℝ))
    (hlarge : 16384*Real.log 2≤(d:ℝ))
    (hcap : firstOrderArrayInformation d R*cap≤(d:ℝ)/16384) :
    pmfEventProbability (firstOrderCoordinateSamplingLaw (PMF.uniformOfFintype ((Fin d → Bool)))
      P Θ A β R hR a₀ i N)
      (fun w => decide (firstOrderStageFast P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ N w.2) i cap N))≤1/32 := by
  have htime (n : ℕ) (hn : n≤N) :
      pmfEventProbability (firstOrderCoordinateSamplingLaw (PMF.uniformOfFintype ((Fin d → Bool)))
        P Θ A β R hR a₀ i N)
        (fun w => decide (firstOrderStageEntry P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ N w.2) i.val n ∧
          firstOrderFastAfterEntry P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ N w.2) i cap n (N-n)))≤
        (1/32)*pmfEventProbability (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ N)
          (fun h => decide (firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ N h) i.val n)) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
    have hh : 256*Real.log (2*(k+1:ℕ))≤(d:ℝ) := by
      apply le_trans _ hhorizon
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.log_le_log (by positivity)
      have hkN : k≤N := by omega
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.succ_le_succ hkN) (by norm_num)
    subst N
    simpa only [Nat.add_sub_cancel_left] using
      firstOrderStageEntry_fast_tape_probability P Θ hd A β R hR i cap dummy a₀ n k hh hlarge hcap
  have hu := pmfEventProbability_union
    (firstOrderCoordinateSamplingLaw (PMF.uniformOfFintype ((Fin d → Bool))) P Θ A β R hR a₀ i N)
    (fun n : Fin (N+1) => fun w => decide
      (firstOrderStageEntry P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ N w.2) i.val n.val ∧
        firstOrderFastAfterEntry P (Function.update Θ i w.1) A β (finiteHistoryTape a₀ N w.2) i cap n.val (N-n.val)))
  simp only [decide_eq_true_eq] at hu
  have hsum := Finset.sum_le_sum (fun (n : Fin (N+1)) (_ : n ∈ Finset.univ) => htime n.val (by omega))
  have htrans := hu.trans hsum
  suffices (1/32)*(∑ n : Fin (N+1), pmfEventProbability (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ N)
      (fun h => decide (firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ N h) i.val n.val)))≤1/32 by
    rw [←Finset.mul_sum] at htrans
    simpa only [firstOrderStageFast, pmfEventProbability_mean, decide_eq_true_eq] using htrans.trans this
  have hs := pmfEventProbability_disjoint_sum_le_one (firstOrderComparisonSamplingLaw P Θ A β R hR a₀ N)
    (fun n : Fin (N+1) => fun h => firstOrderStageEntry P Θ A β (finiteHistoryTape a₀ N h) i.val n.val)
    (fun n k h hn hk => Fin.ext (firstOrderStageEntry_unique P Θ A β _ hn hk))
  linarith only [hs]

end
end SecondOrder

