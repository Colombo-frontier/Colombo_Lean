import NCConcave16991.BranchOracleNativeSampler
import NCConcave16991.BranchOracleHaarBad
import NCConcave16991.BranchOracleTerminalBudget

/-! # The actual static Haar bad event is dominated by the common reservoir tail -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.BranchOracle

open GlobalHard GlobalHardEuclidean MixedHaar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 6000
set_option maxSynthPendingDepth 32
set_option backward.isDefEq.respectTransparency true

variable (n M m D : ℕ) [NeZero n] (hn : 0 < n) (hM : 0 < M) (hD : 0 < D)
  {Ω : Type} [MeasurableSpace Ω]
  (P : StaticPolicy (M := M) (m := m) (Space D) hn Ω)

theorem haar_bad_bound_of_common_support (seed : Ω) (budget : ℕ)
    (hbudget : budget ≤ BranchOracleBudget.budget (n : ℝ) releaseThreshold (M * (m + 1)))
    (hsupport : ∀ᵐ p ∂haarSamplerLaw n M m D budget,
      let θ := (haarRecordedSampler n M m D hn hD P seed budget p).2
      let W := wordReservoirSpan (pureTapeWordReservoir p)
      StaticRunSupported (Space D) hn (haarRotations n M m D θ) (haarSource D hD) W P seed budget ∧
        ∀ j : Fin M, (haarRotations n M m D θ (macroSite m j)).symm
          (returnedSourceProbe (MacroSpaces (ι := Fin n) (Space D) M m) j
            (staticReferenceRun (Space D) hn (haarRotations n M m D θ) (haarSource D hD) P seed budget).1) ∈
          wordSupport (macroSite m j)
            ((staticReferenceRun (Space D) hn (haarRotations n M m D θ) (haarSource D hD) P seed budget).2.profile.words
              (macroSite m j)) W) :
    (staticHaarLaw n M m D).real
      {θ | (seed,θ) ∈ haarBadEvent n M m D hn hD P budget (lastMacro M hM)} ≤
        (wordSliceCount n (M * (m + 1)) (fullMixedCostK M m budget) : ℝ) / ((D : ℝ) * releaseThreshold) := by
  let bad : Set (HaarParameter n M m D) :=
    {θ | (seed,θ) ∈ haarBadEvent n M m D hn hD P budget (lastMacro M hM)}
  let θout := fun p ↦ (haarRecordedSampler n M m D hn hD P seed budget p).2
  let tail : Set (HaarSamplerTape n M m D budget) := {p |
    releaseThreshold ≤ ‖(wordReservoirSpan (pureTapeWordReservoir p)).orthogonalProjectionOnto
      (haarSource D hD)‖ ^ 2}
  have hbad : MeasurableSet bad :=
    (haarBadEvent_measurable n M m D hn hD P budget (lastMacro M hM)).preimage
      (measurable_const.prodMk measurable_id)
  have hp := haarRecordedSampler_hidden_preserving n M m D hn hD P seed budget
  have hsub : θout ⁻¹' bad ≤ᵐ[haarSamplerLaw n M m D budget] tail := by
    filter_upwards [hsupport] with p hs
    intro hb
    by_contra htail
    have hsmall : ‖(wordReservoirSpan (pureTapeWordReservoir p)).orthogonalProjectionOnto
        (haarSource D hD)‖ ^ 2 ≤ releaseThreshold := (lt_of_not_ge htail).le
    have hex := not_staticBad_last_of_supported_budget (Space D) hn hM
      (haarRotations n M m D (θout p)) (haarSource D hD) (haarSource_unit D hD)
      P seed budget hbudget (wordReservoirSpan (pureTapeWordReservoir p)) hs.1 hsmall (hs.2 (lastMacro M hM))
    exact hex hb
  calc
    (staticHaarLaw n M m D).real bad =
        (haarSamplerLaw n M m D budget).real (θout ⁻¹' bad) := by
      unfold Measure.real
      rw [← hp.map_eq,Measure.map_apply hp.measurable hbad]
    _ ≤ (haarSamplerLaw n M m D budget).real tail :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ _ := pure_tape_word_projection_tail
      (vertexFrameTapeLaw (HaarVertexDimension n M m D)) hD ⟨0,hD⟩ releaseThreshold_pos

end NCConcave16991.BranchOracle
