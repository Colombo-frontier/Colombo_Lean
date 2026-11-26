import LowRank.GaussianKernelMean
import LowRank.GaussianOracleConditional
import LowRank.GaussianAmbientConditional

/-! The conditional mean of the actual residual-kernel projector, given
the algorithm's real record, is the nullity ratio times the identity. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section

def matrixCondMean {Ω n : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (m : MeasurableSpace Ω) (A : Ω → Matrix n n ℝ) : Ω → Matrix n n ℝ :=
  fun ω i j => μ[fun z => A z i j | m] ω

theorem gramOracle_residual_kernel_condMean (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0) :
    let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
    let T := fun p => (runGramOracle r s n policy p).1
    matrixCondMean μ (MeasurableSpace.comap T inferInstance)
        (fun p => leftKernelProjector (gramOracleResidual r s n policy p)) =ᵐ[μ]
      (fun _ => (((r : ℝ) - s) / r) • (1 : Matrix (Fin r) (Fin r) ℝ)) := by
  dsimp only
  have he : ∀ i j : Fin r,
      ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
        matrixCondMean (ν.prod (iidMatrixLaw (r + n) (s + n) v))
            (MeasurableSpace.comap (fun p => (runGramOracle r s n policy p).1) inferInstance)
            (fun p => leftKernelProjector (gramOracleResidual r s n policy p)) p i j =
          ((((r : ℝ) - s) / r) • (1 : Matrix (Fin r) (Fin r) ℝ)) i j := by
    intro i j
    have hm : Measurable (fun D : Matrix (Fin r) (Fin s) ℝ => leftKernelProjector D i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_leftKernelProjector)
    have h := gramOracle_conditional_bounded r s n ν policy hunit hv _ hm 1
      (fun D => (leftKernelProjector_isProjector D).entry_norm_le_one i j)
    have hint := congrFun (congrFun (gaussianKernelMean_isotropic r s hs hv) i) j
    change (∫ D, leftKernelProjector D i j ∂iidMatrixLaw r s v) = _ at hint
    simpa only [Function.comp_def, hint] using h
  have hall := (ae_all_iff).mpr (fun i => (ae_all_iff).mpr (he i))
  filter_upwards [hall] with p hp
  ext i j
  exact hp i j

theorem ambientOracle_residual_kernel_condMean (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (r + n) n S)
    (hs : s ≤ r) {v : NNReal} (hv : v ≠ 0) :
    let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
    let T := runAmbientGram r s n policy
    matrixCondMean μ (MeasurableSpace.comap T inferInstance)
        (fun p => leftKernelProjector (ambientOracleResidual r s n policy p)) =ᵐ[μ]
      (fun _ => (((r : ℝ) - s) / r) • (1 : Matrix (Fin r) (Fin r) ℝ)) := by
  dsimp only
  have he : ∀ i j : Fin r,
      ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
        matrixCondMean (ν.prod (iidMatrixLaw (r + n) (s + n) v))
            (MeasurableSpace.comap (runAmbientGram r s n policy) inferInstance)
            (fun p => leftKernelProjector (ambientOracleResidual r s n policy p)) p i j =
          ((((r : ℝ) - s) / r) • (1 : Matrix (Fin r) (Fin r) ℝ)) i j := by
    intro i j
    have hm : Measurable (fun D : Matrix (Fin r) (Fin s) ℝ => leftKernelProjector D i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_leftKernelProjector)
    have h := ambientOracle_conditional_bounded r s n ν policy hv _ hm 1
      (fun D => (leftKernelProjector_isProjector D).entry_norm_le_one i j)
    have hint := congrFun (congrFun (gaussianKernelMean_isotropic r s hs hv) i) j
    change (∫ D, leftKernelProjector D i j ∂iidMatrixLaw r s v) = _ at hint
    simpa only [Function.comp_def, hint] using h
  have hall := (ae_all_iff).mpr (fun i => (ae_all_iff).mpr (he i))
  filter_upwards [hall] with p hp
  ext i j
  exact hp i j

end
end LowRank
