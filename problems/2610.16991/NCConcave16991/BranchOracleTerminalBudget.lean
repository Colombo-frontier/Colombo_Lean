import NCConcave16991.BranchOracleStaticBad
import NCConcave16991.BranchOracleBudget

/-! # Actual paid-call accounting excludes the terminal static bad event -/

noncomputable section

namespace NCConcave16991.BranchOracle

open GlobalHard GlobalHardEuclidean

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem releaseThreshold_le_one : releaseThreshold ≤ 1 := by
  norm_num [releaseThreshold,flatThreshold,deltaGate]

theorem releaseThreshold_terminal_small : releaseThreshold / 4 + releaseThreshold < (1 / 40 : ℝ) ^ 2 := by
  norm_num [releaseThreshold,flatThreshold,deltaGate]

namespace Reference

variable {n M N : ℕ} [NeZero n] (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
  {D : ℝ} (K : KnownDualDomain (dualDimension V) D)
  (B : ∀ j : Fin M, ∀ t : Fin N, BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N)) (ρ : ℝ) (site : Fin M → ℕ) (d c μ : ℝ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension V) Ω)

theorem runAux_released_bound (seed : Ω) (t : ℕ) (s : State (n := n) V K) (hs : s.released ≤ M) :
    (runAux V K B u v ρ site d c μ P seed t s).2.released ≤ M := by
  induction t generalizing s with
  | zero => exact hs
  | succ t ih =>
      cases hn : P.next seed s.history with
      | inl x => simpa only [runAux,hn] using hs
      | inr q => simpa only [runAux,hn] using ih _ (step_released_le V K B u v ρ site d c μ s q hs)

theorem run_released_bound (seed : Ω) (budget : ℕ) :
    (run V K B u v ρ site d c μ P seed budget).2.released ≤ M :=
  runAux_released_bound V K B u v ρ site d c μ P seed budget (initial V K) (Nat.zero_le M)

end Reference

def lastMacro (M : ℕ) (hM : 0 < M) : Fin M := ⟨M - 1,by omega⟩

theorem macroSite_last (M m : ℕ) (hM : 0 < M) : macroSite m (lastMacro M hM) = M * (m + 1) := by
  change (M - 1) * (m + 1) + (m + 1) = M * (m + 1)
  have he : M - 1 + 1 = M := by omega
  calc
    _ = (M - 1 + 1) * (m + 1) := by ring
    _ = _ := by rw [he]

variable {n M m : ℕ} [NeZero n] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] {Ω : Type*} [MeasurableSpace Ω]

theorem static_terminal_mass_le_quarter (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
    (e : E) (P : StaticPolicy (M := M) (m := m) E hn Ω) (seed : Ω) (budget : ℕ)
    (hbudget : budget ≤ BranchOracleBudget.budget (n : ℝ) releaseThreshold (M * (m + 1))) :
    (staticReferenceRun E hn Q e P seed budget).2.profile.mass (M * (m + 1)) ≤ releaseThreshold / 4 := by
  let V := MacroSpaces (ι := Fin n) E M m
  let K := paperDualDomain V hn
  let d := EndpointConstants.endpointD m
  let c := Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m)
  let μ := 1 / ((m : ℝ) + 2) ^ 2
  have hrun := Reference.run_scheduledRun V K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
    releaseThreshold (macroSite (M := M) m) d c μ P seed budget
  have hr := Reference.run_released_bound V K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
    releaseThreshold (macroSite (M := M) m) d c μ P seed budget
  have hk := Reference.runAux_budget V K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
    releaseThreshold (macroSite (M := M) m) d c μ P seed budget (Reference.initial V K)
  have hk' : (staticReferenceRun E hn Q e P seed budget).2.history.1 ≤ budget := by
    simpa only [staticReferenceRun,Reference.run,V,K,d,c,μ,Reference.initial,
      OraclePolicy.emptyHistory,Nat.zero_add] using hk
  have hMH : M ≤ M * (m + 1) := by nlinarith [Nat.zero_le m]
  have hH : 0 < M * (m + 1) := Nat.mul_pos hM (by omega)
  have hh := hrun.terminal_mass_le_quarter releaseThreshold_pos releaseThreshold_le_one M (M * (m + 1))
    hH hr hMH (hk'.trans (by simpa only [Fintype.card_fin] using hbudget))
  simpa only [staticReferenceRun,V,K,d,c,μ,Fintype.card_fin] using hh

theorem not_staticBad_last_of_supported_budget (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
    (e : E) (he : ‖e‖ = 1) (P : StaticPolicy (M := M) (m := m) E hn Ω) (seed : Ω) (budget : ℕ)
    (hbudget : budget ≤ BranchOracleBudget.budget (n : ℝ) releaseThreshold (M * (m + 1)))
    (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (hs : StaticRunSupported E hn Q e W P seed budget)
    (hreservoir : ‖W.orthogonalProjectionOnto e‖ ^ 2 ≤ releaseThreshold)
    (hout : (Q (macroSite m (lastMacro M hM))).symm
      (returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) (lastMacro M hM)
        (staticReferenceRun E hn Q e P seed budget).1) ∈
        wordSupport (macroSite m (lastMacro M hM))
          ((staticReferenceRun E hn Q e P seed budget).2.profile.words (macroSite m (lastMacro M hM))) W) :
    ¬ StaticBadAt E hn Q e P seed budget (lastMacro M hM) := by
  apply not_staticBadAt_of_common_support E hn Q e he P seed budget (lastMacro M hM) W hs hreservoir
  · exact hout
  · rw [macroSite_last]
    have hm := static_terminal_mass_le_quarter E hn hM Q e P seed budget hbudget
    have ht := releaseThreshold_terminal_small
    linarith

end NCConcave16991.BranchOracle
