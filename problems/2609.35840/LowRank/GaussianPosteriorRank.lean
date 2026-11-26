import LowRank.GaussianPosteriorOverlap
import LowRank.ProjectorRank
import LowRank.KernelProjectorGram

/-! Posterior overlap for rank-k outputs, with k the true nullity of the
input. The input dimensions are (k+s+n) by (s+n), and the algorithm makes
exactly n adaptive Gram products. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem ambientOracle_rank_overlap_bound (k s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (k + s + n) n S)
    (hk : 0 < k) {v : NNReal} (hv : v ≠ 0)
    (O : OracleHistory (k + s + n) n S → Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ)
    (hO : Measurable O) (hproj : ∀ h, IsOrthogonalProjector (O h)) (hrank : ∀ h, (O h).rank ≤ k) :
    (∫ p, (O (runAmbientGram (k + s) s n policy p) * leftKernelProjector p.2).trace
      ∂ν.prod (iidMatrixLaw (k + s + n) (s + n) v)) ≤
        2 * (k : ℝ) * (n + k) / (k + s) := by
  have htrace : ∀ h, (O h).trace ≤ ((k + s : ℕ) : ℝ) - s := by
    intro h
    simpa only [Nat.cast_add, add_sub_cancel_right] using (hproj h).trace_le_of_rank_le (hrank h)
  simpa only [Nat.cast_add, add_sub_cancel_right] using
    ambientOracle_posterior_overlap_bound (k + s) s n ν policy (by omega) (by omega) hv O hO hproj htrace

theorem ambientOracle_rank_overlap_tail (k s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (k + s + n) n S)
    (hk : 0 < k) {v : NNReal} (hv : v ≠ 0)
    (O : OracleHistory (k + s + n) n S → Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ)
    (hO : Measurable O) (hproj : ∀ h, IsOrthogonalProjector (O h)) (hrank : ∀ h, (O h).rank ≤ k) :
    (ν.prod (iidMatrixLaw (k + s + n) (s + n) v)).real
      {p | 3 * (k : ℝ) / 4 ≤ (O (runAmbientGram (k + s) s n policy p) * leftKernelProjector p.2).trace} ≤
        (8 / 3) * (n + k) / (k + s) := by
  have htrace : ∀ h, (O h).trace ≤ ((k + s : ℕ) : ℝ) - s := by
    intro h
    simpa only [Nat.cast_add, add_sub_cancel_right] using (hproj h).trace_le_of_rank_le (hrank h)
  simpa only [Nat.cast_add, add_sub_cancel_right] using
    ambientOracle_posterior_overlap_tail (k + s) s n ν policy (by omega) hv O hO hproj htrace

theorem ambientOracle_rank_overlap_tail_constant (k s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (k + s + n) n S)
    (hk : 0 < k) {v : NNReal} (hv : v ≠ 0)
    (O : OracleHistory (k + s + n) n S → Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ)
    (hO : Measurable O) (hproj : ∀ h, IsOrthogonalProjector (O h)) (hrank : ∀ h, (O h).rank ≤ k)
    (hn : (n : ℝ) ≤ (k + s + n : ℝ) / 100) (hkd : (k : ℝ) ≤ (k + s + n : ℝ) / 100) :
    (ν.prod (iidMatrixLaw (k + s + n) (s + n) v)).real
      {p | 3 * (k : ℝ) / 4 ≤ (O (runAmbientGram (k + s) s n policy p) * leftKernelProjector p.2).trace} ≤
        1 / 10 := by
  have htrace : ∀ h, (O h).trace ≤ ((k + s : ℕ) : ℝ) - s := by
    intro h
    simpa only [Nat.cast_add, add_sub_cancel_right] using (hproj h).trace_le_of_rank_le (hrank h)
  have hn' : (n : ℝ) ≤ (((k + s : ℕ) : ℝ) + n) / 100 := by simpa only [Nat.cast_add] using hn
  have hk' : ((k + s : ℕ) : ℝ) - s ≤ (((k + s : ℕ) : ℝ) + n) / 100 := by
    simpa only [Nat.cast_add, add_sub_cancel_right] using hkd
  simpa only [Nat.cast_add, add_sub_cancel_right] using
    ambientOracle_posterior_overlap_tail_constant (k + s) s n ν policy (by omega) hv O hO hproj htrace hn' hk'

theorem gaussianMatrixLaw_ambient_rank_overlap_bound (k s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (k + s + n) n S)
    (hk : 0 < k)
    (O : OracleHistory (k + s + n) n S → Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ)
    (hO : Measurable O) (hproj : ∀ h, IsOrthogonalProjector (O h)) (hrank : ∀ h, (O h).rank ≤ k) :
    (∫ p, (O (runAmbientGram (k + s) s n policy p) * leftKernelProjector p.2).trace
      ∂ν.prod (gaussianMatrixLaw (k + s + n) (s + n))) ≤
        2 * (k : ℝ) * (n + k) / (k + s) := by
  rw [gaussianMatrixLaw_eq_iidMatrixLaw]
  have hv : (k + s + n : NNReal)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (by omega : k + s + n ≠ 0)
  simpa only [Nat.cast_add] using
    ambientOracle_rank_overlap_bound k s n ν policy hk hv O hO hproj hrank

theorem gaussianMatrixLaw_ambient_rank_overlap_tail_constant (k s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (k + s + n) n S)
    (hk : 0 < k)
    (O : OracleHistory (k + s + n) n S → Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ)
    (hO : Measurable O) (hproj : ∀ h, IsOrthogonalProjector (O h)) (hrank : ∀ h, (O h).rank ≤ k)
    (hn : (n : ℝ) ≤ (k + s + n : ℝ) / 100) (hkd : (k : ℝ) ≤ (k + s + n : ℝ) / 100) :
    (ν.prod (gaussianMatrixLaw (k + s + n) (s + n))).real
      {p | 3 * (k : ℝ) / 4 ≤ (O (runAmbientGram (k + s) s n policy p) * leftKernelProjector p.2).trace} ≤
        1 / 10 := by
  rw [gaussianMatrixLaw_eq_iidMatrixLaw]
  have hv : (k + s + n : NNReal)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (by omega : k + s + n ≠ 0)
  simpa only [Nat.cast_add] using
    ambientOracle_rank_overlap_tail_constant k s n ν policy hk hv O hO hproj hrank hn hkd

end
end LowRank
