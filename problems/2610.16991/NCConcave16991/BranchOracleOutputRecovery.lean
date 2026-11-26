import NCConcave16991.BranchOracleProblem
import NCConcave16991.GlobalHardOutputRecovery

/-! # The actual returned output recovers every rotated terminal source -/

noncomputable section

open scoped InnerProductSpace

namespace NCConcave16991.BranchOracle

open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] {n M m : ℕ}

theorem static_stationary_output_source_probe (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ d : ℕ, FormalLayer (ι := Fin n) E d ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E d)
    (e : E) (he : ‖e‖ = 1)
    (c : PrimalSpace (primalDimension (MacroSpaces (ι := Fin n) E M m)))
    (hc : StationaryOutput (staticPaperProblem E hn hM Q e he) c) :
    ∀ j, 1 / 40 ≤ ⟪terminalSources E Q e j,
      returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j c⟫_ℝ := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact stationary_output_source_probe (MacroSpaces (ι := Fin n) E M m) (macroBranches E Q)
    (incomingSources E Q e) (terminalSources E Q e) hn hM
    (incomingSources_unit E Q e he) (terminalSources_unit E Q e he)
    (terminalSources_propagated E Q e) c hc

end NCConcave16991.BranchOracle
