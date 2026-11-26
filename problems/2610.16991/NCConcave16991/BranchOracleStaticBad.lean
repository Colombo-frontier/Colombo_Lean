import NCConcave16991.BranchOracleStaticReduction

/-! # A measurable-oracle bad-event interface avoiding Moreau event disintegration

The event uses only actual reference queries and the original returned source
probe. Every actual stationary output belongs to it. Its exclusion follows
from the genuine common support invariant and terminal projection bound.
-/

noncomputable section

open scoped InnerProductSpace

namespace NCConcave16991.BranchOracle

open GlobalHard GlobalHardEuclidean

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

variable {n M m : ℕ} [NeZero n] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] {Ω : Type*} [MeasurableSpace Ω]

def StaticFlat (hn : 0 < n)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t) (e : E)
    (P : StaticPolicy (M := M) (m := m) E hn Ω) (seed : Ω) (budget : ℕ) : Prop :=
  Reference.RunFlat (MacroSpaces (ι := Fin n) E M m)
    (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)
    (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e) releaseThreshold
    (macroSite (M := M) m) (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) P seed budget
    (Reference.initial (MacroSpaces (ι := Fin n) E M m)
      (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn))

def StaticBadAt (hn : 0 < n)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t) (e : E)
    (P : StaticPolicy (M := M) (m := m) E hn Ω) (seed : Ω) (budget : ℕ) (j : Fin M) : Prop :=
  ¬ StaticFlat E hn Q e P seed budget ∨
    1 / 40 ≤ ⟪terminalSources E Q e j,
      returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j
        (staticReferenceRun E hn Q e P seed budget).1⟫_ℝ

theorem staticReferenceRun_eq_true_of_flat (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
    (e : E) (he : ‖e‖ = 1) (P : StaticPolicy (M := M) (m := m) E hn Ω)
    (seed : Ω) (budget : ℕ) (hf : StaticFlat E hn Q e P seed budget) :
    ((staticReferenceRun E hn Q e P seed budget).1,(staticReferenceRun E hn Q e P seed budget).2.history) =
      OraclePolicy.run (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn) P
        (oracleResponse (staticPaperProblem (m := m) E hn hM Q e he)) seed budget := by
  rw [← trueComponentAnswer_eq_static_oracle E hn hM Q e he]
  exact Reference.runAux_eq_true (MacroSpaces (ι := Fin n) E M m)
    (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)
    (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e) releaseThreshold
    (macroSite (M := M) m) (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) P seed budget
    (Reference.initial (MacroSpaces (ι := Fin n) E M m)
      (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)) hf

theorem stationary_implies_staticBadAt (hn : 0 < n) (hM : 0 < M)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
    (e : E) (he : ‖e‖ = 1) (P : StaticPolicy (M := M) (m := m) E hn Ω)
    (seed : Ω) (budget : ℕ) (j : Fin M)
    (hs : StationaryOutput (staticPaperProblem (m := m) E hn hM Q e he)
      (OraclePolicy.run (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn) P
        (oracleResponse (staticPaperProblem (m := m) E hn hM Q e he)) seed budget).1) :
    StaticBadAt E hn Q e P seed budget j := by
  by_cases hf : StaticFlat E hn Q e P seed budget
  · apply Or.inr
    have ho := congrArg Prod.fst (staticReferenceRun_eq_true_of_flat E hn hM Q e he P seed budget hf)
    apply static_stationary_output_source_probe E hn hM Q e he _ ?_ j
    rw [ho]
    exact hs
  · exact Or.inl hf

theorem not_staticBadAt_of_common_support (hn : 0 < n)
    (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
    (e : E) (he : ‖e‖ = 1) (P : StaticPolicy (M := M) (m := m) E hn Ω)
    (seed : Ω) (budget : ℕ) (j : Fin M) (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (hs : StaticRunSupported E hn Q e W P seed budget)
    (hreservoir : ‖W.orthogonalProjectionOnto e‖ ^ 2 ≤ releaseThreshold)
    (hout : (Q (macroSite m j)).symm
      (returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j (staticReferenceRun E hn Q e P seed budget).1) ∈
        wordSupport (macroSite m j) ((staticReferenceRun E hn Q e P seed budget).2.profile.words (macroSite m j)) W)
    (hsmall : (staticReferenceRun E hn Q e P seed budget).2.profile.mass (macroSite m j) +
      ‖W.orthogonalProjectionOnto e‖ ^ 2 < (1 / 40 : ℝ) ^ 2) :
    ¬ StaticBadAt E hn Q e P seed budget j := by
  have hf : StaticFlat E hn Q e P seed budget :=
    Reference.runFlat_of_supported E (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn) Q e
      (EndpointConstants.endpointD m) (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
      (1 / ((m : ℝ) + 2) ^ 2) W P he seed budget
      (Reference.initial (MacroSpaces (ι := Fin n) E M m)
        (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)) hs hreservoir
  rintro (hnot | hlarge)
  · exact hnot hf
  · have hb := rotated_wordSupport_correlation
      ((staticReferenceRun E hn Q e P seed budget).2.profile.words (macroSite m j)) W e he
      (Q (macroSite m j)) (returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j
        (staticReferenceRun E hn Q e P seed budget).1) hout
      (returnedSourceProbe_norm_le (MacroSpaces (ι := Fin n) E M m) j _)
    change ⟪terminalSources E Q e j,returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j
      (staticReferenceRun E hn Q e P seed budget).1⟫_ℝ ^ 2 ≤
      (staticReferenceRun E hn Q e P seed budget).2.profile.mass (macroSite m j) +
        ‖W.orthogonalProjectionOnto e‖ ^ 2 at hb
    have hp := mul_nonneg (sub_nonneg.mpr hlarge) (by linarith : (0 : ℝ) ≤
      ⟪terminalSources E Q e j,returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j
        (staticReferenceRun E hn Q e P seed budget).1⟫_ℝ + 1 / 40)
    nlinarith

end NCConcave16991.BranchOracle
