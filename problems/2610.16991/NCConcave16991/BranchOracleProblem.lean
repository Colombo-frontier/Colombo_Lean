import NCConcave16991.BranchOracleFamily
import NCConcave16991.GlobalHardPaperProblem
import NCConcave16991.GlobalHardTerminal

/-! # The concrete rotated word family is a genuine smooth saddle problem -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable {n M m : ℕ}

def staticPaperProblem (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ d : ℕ, FormalLayer (ι := Fin n) E d ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E d)
    (e : E) (he : ‖e‖ = 1) :
    Problem (paperParameters n hn M hM m) (primalDimension (MacroSpaces (ι := Fin n) E M m))
      (dualDimension (MacroSpaces (ι := Fin n) E M m)) (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn) := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact paperProblem (MacroSpaces (ι := Fin n) E M m) (macroBranches E Q)
    (incomingSources E Q e) (terminalSources E Q e) hn hM
    (incomingSources_unit E Q e he) (terminalSources_unit E Q e he)

theorem staticPaperProblem_individualSmooth (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ d : ℕ, FormalLayer (ι := Fin n) E d ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E d)
    (e : E) (he : ‖e‖ = 1) : (staticPaperProblem (m := m) E hn hM Q e he).individualSmooth := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact paperProblem_individualSmooth (MacroSpaces (ι := Fin n) E M m) (macroBranches E Q)
    (incomingSources E Q e) (terminalSources E Q e) hn hM
    (incomingSources_unit E Q e he) (terminalSources_unit E Q e he)

theorem staticPaperProblem_averagedSmooth (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ d : ℕ, FormalLayer (ι := Fin n) E d ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E d)
    (e : E) (he : ‖e‖ = 1) : (staticPaperProblem (m := m) E hn hM Q e he).averagedSmooth :=
  (staticPaperProblem (m := m) E hn hM Q e he).individual_implies_averaged
    (staticPaperProblem_individualSmooth (m := m) E hn hM Q e he)

variable [NeZero n]

/-- The fully concrete rotated word family has the actual terminal certificate;
the unit-source and propagation conditions are proved from its definitions. -/
theorem static_small_primal_gradient_all_high
    (Q : ∀ d : ℕ, FormalLayer (ι := Fin n) E d ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E d)
    (e : E) (he : ‖e‖ = 1) (z : GlobalHard.Joint (MacroSpaces (ι := Fin n) E M m))
    (hg : ‖gradient (primalAverageSection (MacroSpaces (ι := Fin n) E M m) (macroBranches E Q)
      (incomingSources E Q e) (terminalSources E Q e) (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
      (1 / ((m : ℝ) + 2) ^ 2) (WithLp.snd z)) (WithLp.fst z)‖ ≤ 1 / 20)
    (hw : WithLp.snd z ∈ Metric.closedBall 0 (publicDualRadius n (m + 2)))
    (hmax : IsMaxOn (fun w ↦ average (MacroSpaces (ι := Fin n) E M m) (macroBranches E Q)
      (incomingSources E Q e) (terminalSources E Q e) (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
      (1 / ((m : ℝ) + 2) ^ 2) (atDual (MacroSpaces (ι := Fin n) E M m) (WithLp.fst z) w))
      (Metric.closedBall 0 (publicDualRadius n (m + 2))) (WithLp.snd z)) :
    ∀ j, 1 ≤ score (MacroSpaces (ι := Fin n) E M m) (terminalSources E Q e) j z := by
  apply maximizing_small_primal_gradient_all_high (MacroSpaces (ι := Fin n) E M m) (macroBranches E Q)
    (incomingSources E Q e) (terminalSources E Q e) z (incomingSources_unit E Q e he)
    (terminalSources_unit E Q e he) (terminalSources_propagated E Q e) hg
  · simpa only [Fintype.card_fin] using hw
  · simpa only [Fintype.card_fin] using hmax

end
end NCConcave16991.BranchOracle
