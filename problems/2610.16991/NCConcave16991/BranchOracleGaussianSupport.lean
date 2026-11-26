import NCConcave16991.BranchOracleNativeSampler
import NCConcave16991.BranchOracleRunConsistency
import NCConcave16991.BranchOracleVertexEngine
import NCConcave16991.MixedHaarProgramWordStream
import NCConcave16991.OracleProgramStateConsistency

/-! # The actual recorded Gaussian branch sampler has common word support -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.BranchOracle

open GlobalHard GlobalHardEuclidean MixedHaar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 6000
set_option maxSynthPendingDepth 32
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] vertexStep vertexFrameComplete referenceMarkedRunProgram

variable (n M m D : ℕ) [NeZero n] (hn : 0 < n) (hD : 0 < D)
  {Ω : Type} [MeasurableSpace Ω]
  (P : StaticPolicy (M := M) (m := m) (Space D) hn Ω)

def haarInitialStream (budget : ℕ) (p : HaarSamplerTape n M m D budget) :
    NativeWordStream (ι := Fin n) (Space D) M m :=
  (initialVertexFrame (HaarVertexDimension n M m D),tapeFreshList (fullMixedCostK M m budget) p)

theorem haarRecordedSampler_record_eq_stream (seed : Ω) (budget : ℕ) (p : HaarSamplerTape n M m D budget) :
    (haarRecordedSampler n M m D hn hD P seed budget p).1.2 =
      (OracleProgram.evalState (OracleProgram.recordReplies (haarMarkedProgram n M m D hn hD P budget))
        (wordStreamOracle (ι := Fin n) (Space D) M m) seed (haarInitialStream n M m D budget p)).1.2 := by
  have h := gaussianEval_eq_evalState
    (OracleProgram.recordReplies (haarMarkedProgram n M m D hn hD P budget))
    (vertexStep (HaarVertexSpace n M m D)) (vertexFrameComplete (HaarVertexDimension n M m D))
    (0 : NativeReply (HaarVertexSpace n M m D)) seed
    (initialVertexFrame (HaarVertexDimension n M m D)) p
  have hh := congrArg (fun r :
      ((HaarMarkedResult n M m D hn × (Fin (fullMixedCostK M m budget) → NativeReply (HaarVertexSpace n M m D))) ×
        HaarParameter n M m D) ↦ r.1.2) h
  simpa only [haarRecordedSampler,nativeProgramSampler,haarInitialStream,wordStreamOracle] using hh

/-- The safe kernel makes this support conclusion total on every generated
Gaussian stream; only consistency with the final static matrix is an a.e. fact. -/
theorem haarRecordedSampler_common_support_ae (seed : Ω) (budget : ℕ) :
    ∀ᵐ p ∂haarSamplerLaw n M m D budget,
      let θ := (haarRecordedSampler n M m D hn hD P seed budget p).2
      let W := wordReservoirSpan (pureTapeWordReservoir p)
      StaticRunSupported (Space D) hn (haarRotations n M m D θ) (haarSource D hD) W P seed budget ∧
        ∀ j : Fin M, (haarRotations n M m D θ (macroSite m j)).symm
          (returnedSourceProbe (MacroSpaces (ι := Fin n) (Space D) M m) j
            (staticReferenceRun (Space D) hn (haarRotations n M m D θ) (haarSource D hD) P seed budget).1) ∈
          wordSupport (macroSite m j)
            ((staticReferenceRun (Space D) hn (haarRotations n M m D θ) (haarSource D hD) P seed budget).2.profile.words
              (macroSite m j)) W := by
  letI := macroJoint_borelSpace (ι := Fin n) (Space D) M m
  letI := macroSources_borelSpace (ι := Fin n) (Space D) M m
  letI := macroActions_borelSpace (ι := Fin n) (Space D) M m
  filter_upwards [haarRecordedSampler_cacheConsistent_ae n M m D hn hD P seed budget] with p hp
  let θ := (haarRecordedSampler n M m D hn hD P seed budget p).2
  let W := wordReservoirSpan (pureTapeWordReservoir p)
  let A := streamWordEngine (ι := Fin n) (Space D) M m W
  let state := haarInitialStream n M m D budget p
  let prog := haarMarkedProgram n M m D hn hD P budget
  let Q := haarRotations n M m D θ
  have hvalid : A.admissible state := by
    intro g hg t w
    exact stream_draw_coordinate_mem_reservoir p g hg t w
  have hcovered : A.Covered W := streamWordEngine_covered (ι := Fin n) (Space D) M m W
  have hroot : LedgerSupported (Space D) M m WordProfile.root W (A.ledger state) :=
    streamWordEngine_initial_supported (ι := Fin n) (Space D) M m W
      (tapeFreshList (fullMixedCostK M m budget) p) WordProfile.root
  have hcache : OracleProgram.CacheConsistent prog (replyOracle (ι := Fin n) (Space D) M m Q) seed
      (OracleProgram.evalState (OracleProgram.recordReplies prog)
        (wordStreamOracle (ι := Fin n) (Space D) M m) seed state).1.2 := by
    rw [← haarRecordedSampler_record_eq_stream n M m D hn hD P seed budget p]
    exact hp
  have hc : OracleProgram.Consistent prog A.oracle (replyOracle (ι := Fin n) (Space D) M m Q) seed state :=
    OracleProgram.consistent_of_recorded_cache prog A.oracle (replyOracle (ι := Fin n) (Space D) M m Q) seed state hcache
  have hc' : OracleProgram.Consistent
      (referenceMarkedRunProgram (Space D) (paperK n M m D hn) (haarSource D hD) releaseThreshold
        (EndpointConstants.endpointD m) (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
        (1 / ((m : ℝ) + 2) ^ 2) P budget)
      A.oracle (replyOracle (ι := Fin n) (Space D) M m Q) seed state := by
    simpa only [prog,haarMarkedProgram] using hc
  have hs := referenceMarkedRun_common_support_of_consistent (Space D) (paperK n M m D hn) A W hcovered
    (haarSource D hD) (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m)) (1 / ((m : ℝ) + 2) ^ 2)
    Q P seed budget state hvalid hroot hc'
  simpa only [StaticRunSupported,staticReferenceRun,paperK] using hs

end NCConcave16991.BranchOracle
