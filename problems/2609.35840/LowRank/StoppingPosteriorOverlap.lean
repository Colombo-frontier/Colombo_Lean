import LowRank.StoppingHardSimulation
import LowRank.GaussianPosteriorRank

/-! The posterior overlap bound for measurable algorithms that may stop early
and query either side of the actual hard matrix H = I - XXᵀ/L. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section

def runBoundedHard (r s n : ℕ) (L : ℝ) {S O : Type*}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy (r + n) O n S)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) : O :=
  runBoundedTwoSided (r + n) n policy (hardMatrix L (wishart p.2)) p.1

set_option maxHeartbeats 1000000 in
theorem measurable_runBoundedHard (r s n : ℕ) (L : ℝ) {S O : Type*}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy (r + n) O n S) :
    Measurable (runBoundedHard r s n L policy) := by
  simpa only [runBoundedHard, Function.comp_def] using
    (measurable_runBoundedTwoSided (r + n) n policy).comp
      (((measurable_hardMatrix (r + n) L).comp
        ((measurable_wishart (r + n) (s + n)).comp
          (measurable_snd : Measurable (Prod.snd :
            S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ → _)))).prodMk measurable_fst)

theorem runBoundedHard_recovery (r s n : ℕ) (L : ℝ) {S O : Type*}
    [MeasurableSpace S] [MeasurableSpace O] (policy : BoundedTwoSidedPolicy (r + n) O n S)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :
    readPaddedHardOutput (r + n) L n policy (identityMemory S)
      (runAmbientGram r s n (padHardPolicy (r + n) L n policy (identityMemory S)) p) =
        runBoundedHard r s n L policy p :=
  padHardPolicy_simulates (r + n) n L policy (identityMemory S) (wishart p.2) (wishart_symmetric p.2) p.1

theorem boundedHard_overlap_bound (k s n : ℕ) (L : ℝ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedTwoSidedPolicy (k + s + n)
      (Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ) n S)
    (hk : 0 < k) {v : NNReal} (hv : v ≠ 0)
    (hout : policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank ≤ k) n) :
    (∫ p, (runBoundedHard (k + s) s n L policy p * leftKernelProjector p.2).trace
      ∂ν.prod (iidMatrixLaw (k + s + n) (s + n) v)) ≤
        2 * (k : ℝ) * (n + k) / (k + s) := by
  have hp := readPaddedHardOutput_property (k + s + n) n L policy (identityMemory S) _ hout
  have h := ambientOracle_rank_overlap_bound k s n ν
    (padHardPolicy (k + s + n) L n policy (identityMemory S)) hk hv
    (readPaddedHardOutput (k + s + n) L n policy (identityMemory S))
    (measurable_readPaddedHardOutput _ _ _ _ _) (fun h => (hp h).1) (fun h => (hp h).2)
  simpa only [runBoundedHard_recovery] using h

theorem boundedHard_overlap_tail (k s n : ℕ) (L : ℝ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedTwoSidedPolicy (k + s + n)
      (Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ) n S)
    (hk : 0 < k) {v : NNReal} (hv : v ≠ 0)
    (hout : policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank ≤ k) n) :
    (ν.prod (iidMatrixLaw (k + s + n) (s + n) v)).real
      {p | 3 * (k : ℝ) / 4 ≤ (runBoundedHard (k + s) s n L policy p * leftKernelProjector p.2).trace} ≤
        (8 / 3) * (n + k) / (k + s) := by
  have hp := readPaddedHardOutput_property (k + s + n) n L policy (identityMemory S) _ hout
  have h := ambientOracle_rank_overlap_tail k s n ν
    (padHardPolicy (k + s + n) L n policy (identityMemory S)) hk hv
    (readPaddedHardOutput (k + s + n) L n policy (identityMemory S))
    (measurable_readPaddedHardOutput _ _ _ _ _) (fun h => (hp h).1) (fun h => (hp h).2)
  simpa only [runBoundedHard_recovery] using h

theorem boundedHard_overlap_tail_constant (k s n : ℕ) (L : ℝ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedTwoSidedPolicy (k + s + n)
      (Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ) n S)
    (hk : 0 < k) {v : NNReal} (hv : v ≠ 0)
    (hout : policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank ≤ k) n)
    (hn : (n : ℝ) ≤ (k + s + n : ℝ) / 100) (hkd : (k : ℝ) ≤ (k + s + n : ℝ) / 100) :
    (ν.prod (iidMatrixLaw (k + s + n) (s + n) v)).real
      {p | 3 * (k : ℝ) / 4 ≤ (runBoundedHard (k + s) s n L policy p * leftKernelProjector p.2).trace} ≤
        1 / 10 := by
  have hp := readPaddedHardOutput_property (k + s + n) n L policy (identityMemory S) _ hout
  have h := ambientOracle_rank_overlap_tail_constant k s n ν
    (padHardPolicy (k + s + n) L n policy (identityMemory S)) hk hv
    (readPaddedHardOutput (k + s + n) L n policy (identityMemory S))
    (measurable_readPaddedHardOutput _ _ _ _ _) (fun h => (hp h).1) (fun h => (hp h).2) hn hkd
  simpa only [runBoundedHard_recovery] using h

theorem gaussianMatrixLaw_boundedHard_overlap_bound (k s n : ℕ) (L : ℝ)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedTwoSidedPolicy (k + s + n)
      (Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ) n S) (hk : 0 < k)
    (hout : policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank ≤ k) n) :
    (∫ p, (runBoundedHard (k + s) s n L policy p * leftKernelProjector p.2).trace
      ∂ν.prod (gaussianMatrixLaw (k + s + n) (s + n))) ≤
        2 * (k : ℝ) * (n + k) / (k + s) := by
  rw [gaussianMatrixLaw_eq_iidMatrixLaw]
  have hv : ((k + s + n : ℕ) : NNReal)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (by omega : k + s + n ≠ 0))
  exact boundedHard_overlap_bound k s n L ν policy hk hv hout

theorem gaussianMatrixLaw_boundedHard_overlap_tail_constant (k s n : ℕ) (L : ℝ)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedTwoSidedPolicy (k + s + n)
      (Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ) n S) (hk : 0 < k)
    (hout : policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank ≤ k) n)
    (hn : (n : ℝ) ≤ (k + s + n : ℝ) / 100) (hkd : (k : ℝ) ≤ (k + s + n : ℝ) / 100) :
    (ν.prod (gaussianMatrixLaw (k + s + n) (s + n))).real
      {p | 3 * (k : ℝ) / 4 ≤ (runBoundedHard (k + s) s n L policy p * leftKernelProjector p.2).trace} ≤
        1 / 10 := by
  rw [gaussianMatrixLaw_eq_iidMatrixLaw]
  have hv : ((k + s + n : ℕ) : NNReal)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (by omega : k + s + n ≠ 0))
  exact boundedHard_overlap_tail_constant k s n L ν policy hk hv hout hn hkd

end
end LowRank
