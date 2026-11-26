import NCConcave16991.BranchOracleCommonEvent
import NCConcave16991.BranchOracleOutputContradiction

/-! # The actual branch reference run reduces to the genuine optimization oracle -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {n M m : ℕ} [NeZero n] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

abbrev StaticState (hn : 0 < n) := Reference.State (n := n) (MacroSpaces (ι := Fin n) E M m)
  (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)

abbrev StaticPolicy (hn : 0 < n) (Ω : Type*) [MeasurableSpace Ω] :=
  OraclePolicy.AdaptivePolicy (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)
    (n := n) (dx := primalDimension (MacroSpaces (ι := Fin n) E M m)) Ω

theorem trueComponentAnswer_eq_static_oracle (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t) (e : E) (he : ‖e‖ = 1) :
    trueComponentAnswer (MacroSpaces (ι := Fin n) E M m) (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)
      (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e) (EndpointConstants.endpointD m)
      (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m)) (1 / ((m : ℝ) + 2) ^ 2) =
      oracleResponse (staticPaperProblem (m := m) E hn hM Q e he) := rfl

variable {Ω : Type*} [MeasurableSpace Ω]

def staticReferenceRun (hn : 0 < n)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t) (e : E)
    (P : StaticPolicy (M := M) (m := m) E hn Ω) (seed : Ω) (budget : ℕ) :
    PrimalSpace (primalDimension (MacroSpaces (ι := Fin n) E M m)) × StaticState (M := M) (m := m) E hn :=
  Reference.run (MacroSpaces (ι := Fin n) E M m) (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)
    (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e) releaseThreshold (macroSite (M := M) m)
    (EndpointConstants.endpointD m) (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) P seed budget

def StaticRunSupported (hn : 0 < n)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t) (e : E)
    (W : Submodule ℝ E) (P : StaticPolicy (M := M) (m := m) E hn Ω) (seed : Ω) (budget : ℕ) : Prop :=
  Reference.RunSupported E (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn) Q e
    (EndpointConstants.endpointD m) (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) W P seed budget
    (Reference.initial (MacroSpaces (ι := Fin n) E M m) (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn))

theorem staticReferenceRun_eq_true_on_common_event (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t) (e : E) (he : ‖e‖ = 1)
    (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (P : StaticPolicy (M := M) (m := m) E hn Ω) (seed : Ω) (budget : ℕ)
    (hs : StaticRunSupported E hn Q e W P seed budget)
    (hreservoir : ‖W.orthogonalProjectionOnto e‖ ^ 2 ≤ releaseThreshold) :
    ((staticReferenceRun E hn Q e P seed budget).1, (staticReferenceRun E hn Q e P seed budget).2.history) =
      OraclePolicy.run (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn) P
        (oracleResponse (staticPaperProblem (m := m) E hn hM Q e he)) seed budget := by
  rw [← trueComponentAnswer_eq_static_oracle E hn hM Q e he]
  exact Reference.runAux_eq_true_on_common_event E (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn) Q e
    (EndpointConstants.endpointD m) (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) W P he seed budget
    (Reference.initial (MacroSpaces (ι := Fin n) E M m) (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)) hs hreservoir

/-- A common support event simultaneously couples the complete transcript
and excludes stationarity of the actual arbitrary returned output. -/
theorem static_true_output_not_stationary (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t) (e : E) (he : ‖e‖ = 1)
    (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (P : StaticPolicy (M := M) (m := m) E hn Ω) (seed : Ω) (budget : ℕ) (j : Fin M)
    (hs : StaticRunSupported E hn Q e W P seed budget)
    (hreservoir : ‖W.orthogonalProjectionOnto e‖ ^ 2 ≤ releaseThreshold)
    (hout : (Q (macroSite m j)).symm
      (returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j (staticReferenceRun E hn Q e P seed budget).1) ∈
        wordSupport (macroSite m j) ((staticReferenceRun E hn Q e P seed budget).2.profile.words (macroSite m j)) W)
    (hsmall : (staticReferenceRun E hn Q e P seed budget).2.profile.mass (macroSite m j) +
      ‖W.orthogonalProjectionOnto e‖ ^ 2 < (1 / 40 : ℝ) ^ 2) :
    ¬StationaryOutput (staticPaperProblem (m := m) E hn hM Q e he)
      (OraclePolicy.run (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn) P
        (oracleResponse (staticPaperProblem (m := m) E hn hM Q e he)) seed budget).1 := by
  have hc := staticReferenceRun_eq_true_on_common_event E hn hM Q e he W P seed budget hs hreservoir
  have ho := congrArg Prod.fst hc
  rw [← ho]
  exact static_not_stationary_of_supported_probe E hn hM Q e he
    (staticReferenceRun E hn Q e P seed budget).2.profile W (staticReferenceRun E hn Q e P seed budget).1 j hout hsmall

end
end NCConcave16991.BranchOracle
