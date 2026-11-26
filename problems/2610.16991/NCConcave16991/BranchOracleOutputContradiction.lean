import NCConcave16991.BranchOracleOutputRecovery
import NCConcave16991.BranchOracleCorrelation

/-! # Actual support rules out a stationary returned output -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

variable {n M m : ℕ} [NeZero n] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- This applies to any returned point, including a point never queried. -/
theorem static_not_stationary_of_supported_probe (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
    (e : E) (he : ‖e‖ = 1) (p : WordProfile (Fin n)) (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (c : PrimalSpace (primalDimension (MacroSpaces (ι := Fin n) E M m))) (j : Fin M)
    (hsupport : (Q (j.val * (m + 1) + (m + 1))).symm
      (returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j c) ∈
        wordSupport (j.val * (m + 1) + (m + 1)) (p.words (j.val * (m + 1) + (m + 1))) W)
    (hsmall : p.mass (j.val * (m + 1) + (m + 1)) + ‖W.orthogonalProjectionOnto e‖ ^ 2 < (1 / 40 : ℝ) ^ 2) :
    ¬StationaryOutput (staticPaperProblem (m := m) E hn hM Q e he) c := by
  intro hc
  have hl := static_stationary_output_source_probe E hn hM Q e he c hc j
  have hb := rotated_wordSupport_correlation (p.words (j.val * (m + 1) + (m + 1))) W e he
    (Q (j.val * (m + 1) + (m + 1))) (returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j c)
    hsupport (returnedSourceProbe_norm_le (MacroSpaces (ι := Fin n) E M m) j c)
  change ⟪terminalSources E Q e j, returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j c⟫_ℝ ^ 2 ≤
    p.mass (j.val * (m + 1) + (m + 1)) + ‖W.orthogonalProjectionOnto e‖ ^ 2 at hb
  have hs := hb.trans_lt hsmall
  have hp := mul_nonneg (sub_nonneg.mpr hl) (by linarith : (0 : ℝ) ≤
    ⟪terminalSources E Q e j, returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j c⟫_ℝ + 1 / 40)
  nlinarith

end
end NCConcave16991.BranchOracle
