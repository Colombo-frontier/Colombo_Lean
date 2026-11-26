import LowRank.GaussianQueryMassBound
import LowRank.GaussianOverlapMean
import LowRank.ProbabilityBounds

/-! The adaptive posterior-overlap bound for actual fixed-horizon Gram
policies on an iid rectangular Gaussian input. Both the cumulative query
mass and the output reduction are proved, rather than supplied as premises.
Here the kernel dimension is r-s and the ambient dimension is r+n. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

theorem gramOracle_posterior_overlap_bound (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r) (hr : 0 < r)
    {v : NNReal} (hv : v ≠ 0)
    (O : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hO : Measurable O) (hproj : ∀ h, IsOrthogonalProjector (O h))
    (htrace : ∀ h, (O h).trace ≤ (r : ℝ) - s) :
    (∫ p, (O (runGramOracle r s n policy p).1 * leftKernelProjector p.2).trace
      ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) ≤
        2 * ((r : ℝ) - s) * (n + ((r : ℝ) - s)) / r := by
  have hp := gramOracle_output_overlap_mean_le r s n ν policy hunit hs hv O hO hproj htrace
  have hm := gramOracleQueryMass_mean_le r s n ν policy hunit hs hr hv
  calc
    _ ≤ _ := hp
    _ ≤ 2 * (((r : ℝ) - s) * n / r) + 2 * (((r : ℝ) - s) / r) * ((r : ℝ) - s) := by linarith
    _ = _ := by ring

theorem ambientOracle_posterior_overlap_bound (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (r + n) n S)
    (hs : s ≤ r) (hr : 0 < r) {v : NNReal} (hv : v ≠ 0)
    (O : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hO : Measurable O) (hproj : ∀ h, IsOrthogonalProjector (O h))
    (htrace : ∀ h, (O h).trace ≤ (r : ℝ) - s) :
    (∫ p, (O (runAmbientGram r s n policy p) * leftKernelProjector p.2).trace
      ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) ≤
        2 * ((r : ℝ) - s) * (n + ((r : ℝ) - s)) / r := by
  have hp := ambientOracle_output_overlap_mean_le r s n ν policy hs hv O hO hproj htrace
  have hm := ambientOracleQueryMass_mean_le r s n ν policy hs hr hv
  calc
    _ ≤ _ := hp
    _ ≤ 2 * (((r : ℝ) - s) * n / r) + 2 * (((r : ℝ) - s) / r) * ((r : ℝ) - s) := by linarith
    _ = _ := by ring

theorem ambientOracle_posterior_overlap_tail (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (r + n) n S)
    (hs : s < r) {v : NNReal} (hv : v ≠ 0)
    (O : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hO : Measurable O) (hproj : ∀ h, IsOrthogonalProjector (O h))
    (htrace : ∀ h, (O h).trace ≤ (r : ℝ) - s) :
    (ν.prod (iidMatrixLaw (r + n) (s + n) v)).real
      {p | 3 * ((r : ℝ) - s) / 4 ≤ (O (runAmbientGram r s n policy p) * leftKernelProjector p.2).trace} ≤
        (8 / 3) * (n + ((r : ℝ) - s)) / r := by
  let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
  let Z := fun p => (O (runAmbientGram r s n policy p) * leftKernelProjector p.2).trace
  have hk : 0 < (r : ℝ) - s := sub_pos.mpr (by exact_mod_cast hs)
  have hi : Integrable Z μ := projector_kernel_overlap_integrable μ
    (O ∘ runAmbientGram r s n policy) Prod.snd
    (hO.comp (measurable_runAmbientGram r s n policy)) measurable_snd
    (fun p => hproj _) (fun p => htrace _)
  have hz : 0 ≤ᵐ[μ] Z := Filter.Eventually.of_forall (fun p =>
    projector_overlap_nonneg (hproj _) (leftKernelProjector_isProjector p.2))
  have hm : (∫ p, Z p ∂μ) ≤
      2 * ((r : ℝ) - s) * (n + ((r : ℝ) - s)) / ((r + n : ℝ) - n) := by
    simpa only [add_sub_cancel_right] using ambientOracle_posterior_overlap_bound r s n ν policy
      hs.le (Nat.zero_lt_of_lt hs) hv O hO hproj htrace
  have ht := overlap_tail_bound (d := (r : ℝ) + n) (q := (n : ℝ)) hk hi hz hm
  simpa only [add_sub_cancel_right] using ht

theorem ambientOracle_posterior_overlap_tail_constant (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (r + n) n S)
    (hs : s < r) {v : NNReal} (hv : v ≠ 0)
    (O : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hO : Measurable O) (hproj : ∀ h, IsOrthogonalProjector (O h))
    (htrace : ∀ h, (O h).trace ≤ (r : ℝ) - s)
    (hn : (n : ℝ) ≤ (r + n : ℝ) / 100) (hk : (r : ℝ) - s ≤ (r + n : ℝ) / 100) :
    (ν.prod (iidMatrixLaw (r + n) (s + n) v)).real
      {p | 3 * ((r : ℝ) - s) / 4 ≤ (O (runAmbientGram r s n policy p) * leftKernelProjector p.2).trace} ≤
        1 / 10 := by
  have hr : 0 < (r : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hs
  have hc := overlap_tail_constant (d := (r : ℝ) + n) (by positivity) hn hk
  simp only [add_sub_cancel_right] at hc
  exact (ambientOracle_posterior_overlap_tail r s n ν policy hs hv O hO hproj htrace).trans hc

end
end LowRank
