import NCConcave16991.BranchOracleJointMeasurable
import NCConcave16991.BranchOracleCachedResponse
import NCConcave16991.BranchOracleRequest
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-! # Actual branch reference measurability from finite rotation actions -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

variable {n M m : ℕ} [NeZero n] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {D : ℝ} (K : KnownDualDomain (dualDimension (MacroSpaces (ι := Fin n) E M m)) D)
variable [BorelSpace (GlobalHard.Joint (MacroSpaces (ι := Fin n) E M m))]
  [OpensMeasurableSpace (SourceParameters (MacroSpaces (ι := Fin n) E M m))]
  [OpensMeasurableSpace (GlobalActionCoordinates (MacroSpaces (ι := Fin n) E M m))]
variable {Θ : Type*} [MeasurableSpace Θ]
  (Q : Θ → ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t)
  (hforward : ∀ t : Vertex M m, Measurable (fun a : Θ × VertexLayer (ι := Fin n) E M m t ↦ Q a.1 t.val a.2))
  (hinverse : ∀ t : Vertex M m, Measurable (fun a : Θ × VertexLayer (ι := Fin n) E M m t ↦ (Q a.1 t.val).symm a.2))
  (e : E)

include hforward

theorem incomingSources_joint_measurable : Measurable (fun θ ↦ incomingSources (M := M) (m := m) E (Q θ) e) := by
  apply measurable_pi_iff.mpr
  intro j
  convert (hforward (depthVertex M m j 0)).comp (measurable_id.prodMk measurable_const) using 1 <;> rfl

theorem terminalSources_joint_measurable : Measurable (fun θ ↦ terminalSources (M := M) (m := m) E (Q θ) e) := by
  apply measurable_pi_iff.mpr
  intro j
  convert (hforward (depthVertex M m j (Fin.last (m + 1)))).comp (measurable_id.prodMk measurable_const) using 1 <;> rfl

theorem knownSources_joint_measurable : Measurable (fun a : Θ × ℕ ↦
    (knownIncoming (MacroSpaces (ι := Fin n) E M m) a.2 (incomingSources E (Q a.1) e),
     knownTerminal (MacroSpaces (ι := Fin n) E M m) a.2 (terminalSources E (Q a.1) e))) := by
  apply measurable_from_prod_countable_left
  intro r
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro j
    by_cases hj : j.val ≤ r
    · convert (measurable_pi_apply j).comp (incomingSources_joint_measurable E Q hforward e) using 1
      funext θ
      simp only [knownIncoming, if_pos hj, Function.comp_apply]
    · simpa only [knownIncoming, if_neg hj] using
        (measurable_const : Measurable (fun _ : Θ ↦ (0 : MacroSpaces (ι := Fin n) E M m j 0)))
  · apply measurable_pi_iff.mpr
    intro j
    by_cases hj : j.val < r
    · convert (measurable_pi_apply j).comp (terminalSources_joint_measurable E Q hforward e) using 1
      funext θ
      simp only [knownTerminal, if_pos hj, Function.comp_apply]
    · simpa only [knownTerminal, if_neg hj] using
        (measurable_const : Measurable (fun _ : Θ ↦ (0 : MacroSpaces (ι := Fin n) E M m j (Fin.last (m + 1)))))

include hinverse

theorem macroForward_joint_measurable (i : Fin n) (j : Fin M) (k : Fin (m + 1)) : Measurable
    (fun a : Θ × GlobalHard.Joint (MacroSpaces (ι := Fin n) E M m) ↦
      (macroBranches E (Q a.1) j k).branch i
        (((PiLp.proj (𝕜 := ℝ) 2 (MacroSpaces (ι := Fin n) E M m j) k.castSucc).comp
          (dualProj (MacroSpaces (ι := Fin n) E M m) j)) a.2)) := by
  let p := (PiLp.proj (𝕜 := ℝ) 2 (MacroSpaces (ι := Fin n) E M m j) k.castSucc).comp
    (dualProj (MacroSpaces (ι := Fin n) E M m) j)
  have hi := (hinverse (depthVertex M m j k.castSucc)).comp
    (measurable_fst.prodMk (p.continuous.measurable.comp measurable_snd))
  have hf := (hforward (depthVertex M m j k.succ)).comp
    (measurable_fst.prodMk ((prependIsometry E (j.val * (m + 1) + k.val) i).continuous.measurable.comp hi))
  convert hf using 1 <;> rfl

theorem macroTranspose_joint_measurable (i : Fin n) (j : Fin M) (k : Fin (m + 1)) : Measurable
    (fun a : Θ × GlobalHard.Joint (MacroSpaces (ι := Fin n) E M m) ↦
      ((macroBranches E (Q a.1) j k).branch i).toContinuousLinearMap.adjoint
        (((PiLp.proj (𝕜 := ℝ) 2 (MacroSpaces (ι := Fin n) E M m j) k.succ).comp
          (dualProj (MacroSpaces (ι := Fin n) E M m) j)) a.2)) := by
  let p := (PiLp.proj (𝕜 := ℝ) 2 (MacroSpaces (ι := Fin n) E M m j) k.succ).comp
    (dualProj (MacroSpaces (ι := Fin n) E M m) j)
  have hi := (hinverse (depthVertex M m j k.succ)).comp
    (measurable_fst.prodMk (p.continuous.measurable.comp measurable_snd))
  have hs : Continuous (slice E (j.val * (m + 1) + k.val) i) := by
    convert ((formalBranchFamily E (j.val * (m + 1) + k.val)).branch i).toContinuousLinearMap.adjoint.continuous using 1
    funext y
    exact (formalBranch_adjoint_apply E (j.val * (m + 1) + k.val) i y).symm
  have hf := (hforward (depthVertex M m j k.castSucc)).comp
    (measurable_fst.prodMk (hs.measurable.comp hi))
  convert hf using 1 <;> first | rfl | (funext a; exact macroBranch_transpose E (Q a.1) j k i (p a.2))

theorem actionCoordinates_joint_measurable : Measurable
    (fun a : Fin n × (Θ × GlobalHard.Joint (MacroSpaces (ι := Fin n) E M m)) ↦
      actionCoordinates (MacroSpaces (ι := Fin n) E M m) (macroBranches E (Q a.2.1)) a.1 a.2.2) := by
  apply measurable_from_prod_countable_right
  intro i
  apply measurable_pi_iff.mpr
  intro j
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro k
    convert macroForward_joint_measurable E Q hforward hinverse i j k using 1 <;> rfl
  · apply measurable_pi_iff.mpr
    intro k
    convert macroTranspose_joint_measurable E Q hforward hinverse i j k using 1 <;> rfl

theorem referenceResponse_joint_measurable (d c μ : ℝ) : Measurable
    (fun a : Θ × (ℕ × OracleQuery n (primalDimension (MacroSpaces (ι := Fin n) E M m)) K) ↦
      referenceResponse (MacroSpaces (ι := Fin n) E M m) K (macroBranches E (Q a.1))
        (incomingSources E (Q a.1) e) (terminalSources E (Q a.1) e) a.2.1 d c μ a.2.2) := by
  let X := Θ × (ℕ × OracleQuery n (primalDimension (MacroSpaces (ι := Fin n) E M m)) K)
  let input : X → CachedReplyInput (n := n) (MacroSpaces (ι := Fin n) E M m) K := fun a ↦
    (((knownIncoming (MacroSpaces (ι := Fin n) E M m) a.2.1 (incomingSources E (Q a.1) e),
        knownTerminal (MacroSpaces (ι := Fin n) E M m) a.2.1 (terminalSources E (Q a.1) e)), a.2.2),
      actionCoordinates (MacroSpaces (ι := Fin n) E M m) (macroBranches E (Q a.1)) a.2.2.1
        (queryGlobal (MacroSpaces (ι := Fin n) E M m) K a.2.2))
  have hz : Measurable (fun a : X ↦ queryGlobal (MacroSpaces (ι := Fin n) E M m) K a.2.2) :=
    (queryGlobal_continuous (MacroSpaces (ι := Fin n) E M m) K).measurable.comp (measurable_snd.comp measurable_snd)
  have hs : Measurable (fun a : X ↦ (input a).1.1) := (knownSources_joint_measurable E Q hforward e).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have ha : Measurable (fun a : X ↦ (input a).2) := (actionCoordinates_joint_measurable E Q hforward hinverse).comp
    ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk (measurable_fst.prodMk hz))
  have hi : Measurable input := (hs.prodMk (measurable_snd.comp measurable_snd)).prodMk ha
  convert (renderCachedAnswer_measurable (MacroSpaces (ι := Fin n) E M m) K d c μ).comp hi using 1
  funext a
  simp only [Function.comp_apply, input, renderCachedAnswer, referenceResponse, coordinateArray_actionCoordinates]

omit hinverse in
theorem sourceScore_joint_measurable (j : Fin M) : Measurable
    (fun a : Θ × OracleQuery n (primalDimension (MacroSpaces (ι := Fin n) E M m)) K ↦
      stateScore (terminalSources E (Q a.1) e j)
        (stateProj (MacroSpaces (ι := Fin n) E M m) j
          (queryGlobal (MacroSpaces (ι := Fin n) E M m) K a.2))) := by
  have hv : Measurable (fun a : Θ × OracleQuery n (primalDimension (MacroSpaces (ι := Fin n) E M m)) K ↦
      terminalSources E (Q a.1) e j) :=
    ((measurable_pi_apply j).comp (terminalSources_joint_measurable E Q hforward e)).comp measurable_fst
  have hs : Measurable (fun a : Θ × OracleQuery n (primalDimension (MacroSpaces (ι := Fin n) E M m)) K ↦
      stateProj (MacroSpaces (ι := Fin n) E M m) j (queryGlobal (MacroSpaces (ι := Fin n) E M m) K a.2)) :=
    (stateProj (MacroSpaces (ι := Fin n) E M m) j).continuous.measurable.comp
    ((queryGlobal_continuous (MacroSpaces (ι := Fin n) E M m) K).measurable.comp measurable_snd)
  exact hv.inner ((LocalizationRadial.radialCap_contDiff (by norm_num : (0 : ℝ) < 10)).continuous.measurable.comp hs)

end
end NCConcave16991.BranchOracle
