import LowRank.GaussianKernelBottom
import LowRank.MatrixConditionalOrder

/-! The posterior of the actual input-kernel projector, expressed in the
algorithm's query basis. Its hidden block is bounded conditionally on the
actual oracle record, not merely after taking an unconditional mean. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def gramOracleKernelPosterior (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) (policy : VisibleOraclePolicy (r + n) r n 0 S) (v : NNReal) :=
  matrixCondMean (ν.prod (iidMatrixLaw (r + n) (s + n) v))
    (MeasurableSpace.comap (fun p => (runGramOracle r s n policy p).1) inferInstance)
    (gramOracleKernelCoordinates r s n policy)

theorem gramOracleKernelPosterior_posSemidef (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (v : NNReal) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      (gramOracleKernelPosterior r s n ν policy v p).PosSemidef := by
  apply matrixCondMean_posSemidef _ _ _ (gramOracleKernelCoordinates_entryIntegrable r s n policy _)
  exact Filter.Eventually.of_forall (fun p =>
    (gramOracleKernelCoordinates_isProjector r s n policy p).posSemidef)

theorem gramOracleKernelPosterior_bottom_le (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      LoewnerLE ((gramOracleKernelPosterior r s n ν policy v p).submatrix Sum.inr Sum.inr)
        ((((r : ℝ) - s) / r) • (1 : Matrix (Fin r) (Fin r) ℝ)) := by
  let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
  let R := gramOracleResidual r s n policy
  have hR : MeasurePreserving R μ (iidMatrixLaw r s v) :=
    ⟨measurable_gramOracleResidual r s n policy, gramOracle_residual_law r s n ν policy v⟩
  have hQ : EntryIntegrable (fun p => leftKernelProjector (R p)) μ := by
    intro i j
    have hm : Measurable (fun D : Matrix (Fin r) (Fin s) ℝ => leftKernelProjector D i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_leftKernelProjector)
    exact (hR.integrable_comp hm.stronglyMeasurable.aestronglyMeasurable).mpr
      (leftKernelProjector_entryIntegrable (iidMatrixLaw r s v) i j)
  have hle := matrixCondMean_mono
    (MeasurableSpace.comap (fun p => (runGramOracle r s n policy p).1) inferInstance) μ
    (fun p => (gramOracleKernelCoordinates r s n policy p).submatrix Sum.inr Sum.inr)
    (fun p => leftKernelProjector (R p))
    (fun i j => gramOracleKernelCoordinates_entryIntegrable r s n policy μ (Sum.inr i) (Sum.inr j))
    hQ (gramOracle_kernel_bottom_le_ae r s n ν policy hunit hs hv)
  filter_upwards [hle, gramOracle_residual_kernel_condMean r s n ν policy hunit hs hv] with p hp he
  rw [he] at hp
  exact hp

end
end LowRank
