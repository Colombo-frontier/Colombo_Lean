import NCConcave16991.BranchOracleStaticBad
import NCConcave16991.BranchOracleRotationMeasurable

/-! # Actual jointly measurable static bad event for arbitrary private seeds -/

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.BranchOracle

open GlobalHard GlobalHardEuclidean

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

variable {n M m : ℕ} [NeZero n] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [BorelSpace (GlobalHard.Joint (MacroSpaces (ι := Fin n) E M m))]
  [OpensMeasurableSpace (SourceParameters (MacroSpaces (ι := Fin n) E M m))]
  [OpensMeasurableSpace (GlobalActionCoordinates (MacroSpaces (ι := Fin n) E M m))]

variable {Θ : Type*} [MeasurableSpace Θ]
  (Q : Θ → ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
  (hforward : ∀ t : Vertex M m, Measurable (fun a : Θ × VertexLayer (ι := Fin n) E M m t ↦ Q a.1 t.val a.2))
  (hinverse : ∀ t : Vertex M m, Measurable (fun a : Θ × VertexLayer (ι := Fin n) E M m t ↦ (Q a.1 t.val).symm a.2))
  (e : E) (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
  (P : StaticPolicy (M := M) (m := m) E hn Ω)

include hforward hinverse in
theorem staticReferenceRun_joint_measurable (budget : ℕ) :
    Measurable (fun a : Θ × Ω ↦ staticReferenceRun E hn (Q a.1) e P a.2 budget) := by
  exact Reference.run_joint_measurable (MacroSpaces (ι := Fin n) E M m)
    (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)
    (fun θ ↦ macroBranches E (Q θ)) (fun θ ↦ incomingSources E (Q θ) e)
    (fun θ ↦ terminalSources E (Q θ) e) releaseThreshold (macroSite (M := M) m)
    (EndpointConstants.endpointD m) (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2)
    (referenceResponse_joint_measurable E (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)
      Q hforward hinverse e _ _ _) P budget

include hforward hinverse in
theorem staticFlat_joint_measurable (budget : ℕ) :
    Measurable (fun a : Θ × Ω ↦ StaticFlat E hn (Q a.1) e P a.2 budget) := by
  exact Reference.runFlat_initial_joint_measurable (MacroSpaces (ι := Fin n) E M m)
    (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)
    (fun θ ↦ macroBranches E (Q θ)) (fun θ ↦ incomingSources E (Q θ) e)
    (fun θ ↦ terminalSources E (Q θ) e) releaseThreshold (macroSite (M := M) m)
    (EndpointConstants.endpointD m) (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2)
    (referenceResponse_joint_measurable E (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)
      Q hforward hinverse e _ _ _) P
    (fun j ↦ sourceScore_joint_measurable E (paperDualDomain (MacroSpaces (ι := Fin n) E M m) hn)
      Q hforward e j) budget

include hforward hinverse in
theorem staticBadAt_joint_measurable (budget : ℕ) (j : Fin M) :
    Measurable (fun a : Θ × Ω ↦ StaticBadAt E hn (Q a.1) e P a.2 budget j) := by
  have hr := staticReferenceRun_joint_measurable E Q hforward hinverse e hn P budget
  have hv : Measurable (fun a : Θ × Ω ↦ terminalSources E (Q a.1) e j) :=
    ((measurable_pi_apply j).comp (terminalSources_joint_measurable E Q hforward e)).comp measurable_fst
  have hprobe : Measurable (fun a : Θ × Ω ↦ returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j
      (staticReferenceRun E hn (Q a.1) e P a.2 budget).1) := by
    have hc : Continuous (returnedSourceProbe (MacroSpaces (ι := Fin n) E M m) j) :=
      ((LocalizationRadial.radialCap_contDiff (by norm_num : (0 : ℝ) < 10)).continuous.comp
        ((primalStateProjection (MacroSpaces (ι := Fin n) E M m) j).continuous.comp
          (primalCoordinates (MacroSpaces (ι := Fin n) E M m)).symm.continuous)).const_smul (1 / 20 : ℝ)
    exact hc.measurable.comp (measurable_fst.comp hr)
  exact (staticFlat_joint_measurable E Q hforward hinverse e hn P budget).not.or
    (measurableSet_setOfPred.mp (measurableSet_le measurable_const (hv.inner hprobe)))

def staticBadEvent (budget : ℕ) (j : Fin M) : Set (Ω × Θ) :=
  {a | StaticBadAt E hn (Q a.2) e P a.1 budget j}

include hforward hinverse in
theorem staticBadEvent_measurable (budget : ℕ) (j : Fin M) :
    MeasurableSet (staticBadEvent E Q e hn P budget j) :=
  measurableSet_setOfPred.mpr
    ((staticBadAt_joint_measurable E Q hforward hinverse e hn P budget j).comp measurable_swap)

end NCConcave16991.BranchOracle
