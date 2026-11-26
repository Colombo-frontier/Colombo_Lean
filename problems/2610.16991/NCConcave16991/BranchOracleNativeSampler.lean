import NCConcave16991.BranchOracleHaarFamily
import NCConcave16991.BranchOracleRunProgram
import NCConcave16991.BranchOracleStaticReduction
import NCConcave16991.MixedHaarNativeProgramLaw
import NCConcave16991.MixedHaarProgramRecordLaw

/-! # The actual branch reference program under its native Gaussian/Haar sampler -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.BranchOracle

open GlobalHard GlobalHardEuclidean MixedHaar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 6000
set_option maxSynthPendingDepth 32
set_option backward.isDefEq.respectTransparency true

variable (n M m D : ℕ) [NeZero n]

attribute [local irreducible] nativeCoordinates nativeVertexOperator nativeRequestAnswer haarRotations

theorem nativeRequestAnswer_eq_replyOracle (θ : HaarParameter n M m D) :
    nativeRequestAnswer (HaarVertexSpace n M m D) θ =
      replyOracle (ι := Fin n) (Space D) M m (haarRotations n M m D θ) := by
  funext q i
  rcases q with ⟨t,a | b⟩
  · by_cases hi : i = t
    · subst i
      rw [replyOracle_at_request,nativeRequestAnswer_forward]
      change nativeVertexOperator (HaarVertexSpace n M m D) θ t a = haarRotations n M m D θ t.val a
      rw [haarRotations_vertex]
    · rw [nativeRequestAnswer_unselected _ _ _ _ (Ne.symm hi)]
      exact (fillReply_other (ι := Fin n) (Space D) M m t i _ hi).symm
  · by_cases hi : i = t
    · subst i
      rw [replyOracle_at_request,nativeRequestAnswer_inverse]
      change (nativeVertexOperator (HaarVertexSpace n M m D) θ t).symm b =
        (haarRotations n M m D θ t.val).symm b
      rw [haarRotations_vertex]
    · rw [nativeRequestAnswer_unselected _ _ _ _ (Ne.symm hi)]
      exact (fillReply_other (ι := Fin n) (Space D) M m t i _ hi).symm

abbrev paperK (hn : 0 < n) := paperDualDomain (MacroSpaces (ι := Fin n) (Space D) M m) hn

abbrev fullMixedCostK (budget : ℕ) := fullMixedCost (M := M) (m := m) budget

abbrev HaarMarkedResult (hn : 0 < n) :=
  ReferenceResult (Space D) (paperK n M m D hn) × NativeReply (HaarVertexSpace n M m D)

variable (hn : 0 < n) (hD : 0 < D) {Ω : Type} [MeasurableSpace Ω]
  (P : StaticPolicy (M := M) (m := m) (Space D) hn Ω)

def haarMarkedProgram (budget : ℕ) :
    OracleProgram.Fixed (NativeRequest (HaarVertexSpace n M m D)) (NativeReply (HaarVertexSpace n M m D))
      (HaarMarkedResult n M m D hn) Ω (fullMixedCostK M m budget) := by
  letI := macroJoint_borelSpace (ι := Fin n) (Space D) M m
  letI := macroSources_borelSpace (ι := Fin n) (Space D) M m
  letI := macroActions_borelSpace (ι := Fin n) (Space D) M m
  exact referenceMarkedRunProgram (Space D) (paperK n M m D hn) (haarSource D hD) releaseThreshold
    (EndpointConstants.endpointD m) (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) P budget

def haarStaticMarkedResult (seed : Ω) (budget : ℕ) (θ : HaarParameter n M m D) : HaarMarkedResult n M m D hn :=
  (staticReferenceRun (Space D) hn (haarRotations n M m D θ) (haarSource D hD) P seed budget,
    fun t : Vertex M m ↦ (haarRotations n M m D θ t.val).symm (outputMark (Space D) M m t.val
      (staticReferenceRun (Space D) hn (haarRotations n M m D θ) (haarSource D hD) P seed budget).1))

theorem eval_haarMarkedProgram (seed : Ω) (budget : ℕ) (θ : HaarParameter n M m D) :
    OracleProgram.eval (haarMarkedProgram n M m D hn hD P budget)
      (nativeRequestAnswer (HaarVertexSpace n M m D) θ) seed =
        haarStaticMarkedResult n M m D hn hD P seed budget θ := by
  letI := macroJoint_borelSpace (ι := Fin n) (Space D) M m
  letI := macroSources_borelSpace (ι := Fin n) (Space D) M m
  letI := macroActions_borelSpace (ι := Fin n) (Space D) M m
  rw [nativeRequestAnswer_eq_replyOracle]
  unfold haarMarkedProgram haarStaticMarkedResult
  rw [eval_referenceMarkedRunProgram]
  rfl

abbrev HaarSamplerTape (budget : ℕ) :=
  RevealTape (GaussianVertexBlock n (M * (m + 1)) D)
    (VertexFrameTape (HaarVertexDimension n M m D)) (fullMixedCostK M m budget)

def haarSamplerLaw (budget : ℕ) : Measure (HaarSamplerTape n M m D budget) :=
  revealTapeLaw (gaussianVertexLaw n (M * (m + 1)) D)
    (vertexFrameTapeLaw (HaarVertexDimension n M m D)) (fullMixedCostK M m budget)

instance haarSamplerLaw_probability (budget : ℕ) : IsProbabilityMeasure (haarSamplerLaw n M m D budget) := by
  unfold haarSamplerLaw
  infer_instance

def haarRecordedSampler (seed : Ω) (budget : ℕ) : HaarSamplerTape n M m D budget →
    ((HaarMarkedResult n M m D hn × (Fin (fullMixedCostK M m budget) → NativeReply (HaarVertexSpace n M m D))) ×
      HaarParameter n M m D) :=
  nativeProgramSampler (HaarVertexSpace n M m D)
    (OracleProgram.recordReplies (haarMarkedProgram n M m D hn hD P budget)) seed

theorem haarRecordedSampler_hidden_preserving (seed : Ω) (budget : ℕ) :
    MeasurePreserving (fun p ↦ (haarRecordedSampler n M m D hn hD P seed budget p).2)
      (haarSamplerLaw n M m D budget) (staticHaarLaw n M m D) := by
  simpa only [haarRecordedSampler,haarSamplerLaw,nativeGaussianFamilyLaw,gaussianVertexLaw,staticHaarLaw] using
    nativeProgram_hidden_preserving (HaarVertexSpace n M m D)
      (OracleProgram.recordReplies (haarMarkedProgram n M m D hn hD P budget)) seed

theorem haarRecordedSampler_cacheConsistent_ae (seed : Ω) (budget : ℕ) :
    ∀ᵐ p ∂haarSamplerLaw n M m D budget,
      let out := haarRecordedSampler n M m D hn hD P seed budget p
      OracleProgram.CacheConsistent (haarMarkedProgram n M m D hn hD P budget)
        (replyOracle (ι := Fin n) (Space D) M m (haarRotations n M m D out.2)) seed out.1.2 := by
  have h := programGaussianEval_cacheConsistent_ae (haarMarkedProgram n M m D hn hD P budget)
    (vertexStep (HaarVertexSpace n M m D)) (vertexFrameComplete (HaarVertexDimension n M m D))
    (nativeRequestAnswer (HaarVertexSpace n M m D)) (nativeGaussianFamilyLaw (HaarVertexSpace n M m D))
    (vertexFrameTapeLaw (HaarVertexDimension n M m D))
    (vertexStep_measurable (HaarVertexSpace n M m D))
    (vertexFrameComplete_measurable (HaarVertexDimension n M m D))
    (nativeRequestAnswer_measurable (HaarVertexSpace n M m D))
    (vertexStep_answer_local_jointLaw (HaarVertexSpace n M m D)) seed
    (initialVertexFrame (HaarVertexDimension n M m D))
  simpa only [haarRecordedSampler,nativeProgramSampler,haarSamplerLaw,nativeGaussianFamilyLaw,
    gaussianVertexLaw,nativeRequestAnswer_eq_replyOracle] using h

theorem haarRecordedSampler_eq_static_ae (seed : Ω) (budget : ℕ) :
    ∀ᵐ p ∂haarSamplerLaw n M m D budget,
      let out := haarRecordedSampler n M m D hn hD P seed budget p
      out.1.1 = haarStaticMarkedResult n M m D hn hD P seed budget out.2 := by
  have h := programGaussianEval_eq_static_ae (haarMarkedProgram n M m D hn hD P budget)
    (vertexStep (HaarVertexSpace n M m D)) (vertexFrameComplete (HaarVertexDimension n M m D))
    (nativeRequestAnswer (HaarVertexSpace n M m D)) (nativeGaussianFamilyLaw (HaarVertexSpace n M m D))
    (vertexFrameTapeLaw (HaarVertexDimension n M m D))
    (vertexStep_measurable (HaarVertexSpace n M m D))
    (vertexFrameComplete_measurable (HaarVertexDimension n M m D))
    (nativeRequestAnswer_measurable (HaarVertexSpace n M m D))
    (vertexStep_answer_local_jointLaw (HaarVertexSpace n M m D)) seed
    (initialVertexFrame (HaarVertexDimension n M m D))
  simpa only [haarRecordedSampler,nativeProgramSampler,haarSamplerLaw,nativeGaussianFamilyLaw,
    gaussianVertexLaw,eval_haarMarkedProgram] using h

def haarMarkedSampleTheta (seed : Ω) (budget : ℕ) (p : HaarSamplerTape n M m D budget) :
    HaarParameter n M m D := (haarRecordedSampler n M m D hn hD P seed budget p).2

def haarMarkedSampleResult (seed : Ω) (budget : ℕ) (p : HaarSamplerTape n M m D budget) :
    HaarMarkedResult n M m D hn := (haarRecordedSampler n M m D hn hD P seed budget p).1.1

def haarMarkedSampleRecord (seed : Ω) (budget : ℕ) (p : HaarSamplerTape n M m D budget) :
    Fin (fullMixedCostK M m budget) → NativeReply (HaarVertexSpace n M m D) :=
  (haarRecordedSampler n M m D hn hD P seed budget p).1.2

theorem haarMarkedSampleTheta_preserving (seed : Ω) (budget : ℕ) :
    MeasurePreserving (haarMarkedSampleTheta n M m D hn hD P seed budget)
      (haarSamplerLaw n M m D budget) (staticHaarLaw n M m D) :=
  haarRecordedSampler_hidden_preserving n M m D hn hD P seed budget

theorem haarMarkedSampleTheta_law (seed : Ω) (budget : ℕ) :
    (haarSamplerLaw n M m D budget).map (haarMarkedSampleTheta n M m D hn hD P seed budget) =
      staticHaarLaw n M m D := (haarMarkedSampleTheta_preserving n M m D hn hD P seed budget).map_eq

theorem haarMarkedSampleResult_eq_finish (seed : Ω) (budget : ℕ) (p : HaarSamplerTape n M m D budget) :
    haarMarkedSampleResult n M m D hn hD P seed budget p =
      (haarMarkedProgram n M m D hn hD P budget).finish seed
        (haarMarkedSampleRecord n M m D hn hD P seed budget p) := by
  simpa only [haarMarkedSampleResult,haarMarkedSampleRecord,haarRecordedSampler,nativeProgramSampler,programGaussianEval] using
    programGaussianEvalFrom_record_finish (haarMarkedProgram n M m D hn hD P budget)
      (vertexStep (HaarVertexSpace n M m D)) (vertexFrameComplete (HaarVertexDimension n M m D))
      seed (fullMixedCostK M m budget) 0 (by omega)
      (initialVertexFrame (HaarVertexDimension n M m D)) Fin.elim0 p

theorem haarMarkedSampleResult_eq_reference_ae (seed : Ω) (budget : ℕ) :
    ∀ᵐ p ∂haarSamplerLaw n M m D budget,
      haarMarkedSampleResult n M m D hn hD P seed budget p =
        haarStaticMarkedResult n M m D hn hD P seed budget
          (haarMarkedSampleTheta n M m D hn hD P seed budget p) :=
  haarRecordedSampler_eq_static_ae n M m D hn hD P seed budget

theorem haarMarkedSampleRecord_eq_static_ae (seed : Ω) (budget : ℕ) :
    ∀ᵐ p ∂haarSamplerLaw n M m D budget,
      haarMarkedSampleRecord n M m D hn hD P seed budget p =
        (OracleProgram.eval (OracleProgram.recordReplies (haarMarkedProgram n M m D hn hD P budget))
          (replyOracle (ι := Fin n) (Space D) M m
            (haarRotations n M m D (haarMarkedSampleTheta n M m D hn hD P seed budget p))) seed).2 := by
  filter_upwards [haarRecordedSampler_cacheConsistent_ae n M m D hn hD P seed budget] with p hp
  let prog := haarMarkedProgram n M m D hn hD P budget
  let A := replyOracle (ι := Fin n) (Space D) M m
    (haarRotations n M m D (haarMarkedSampleTheta n M m D hn hD P seed budget p))
  let cache := haarMarkedSampleRecord n M m D hn hD P seed budget p
  have hc : OracleProgram.CacheConsistent (OracleProgram.recordReplies prog) A seed cache := hp
  have hh := OracleProgram.CacheConsistent.finish_eq_eval (OracleProgram.recordReplies prog) A seed cache hc
  simpa only [OracleProgram.recordReplies] using congrArg Prod.snd hh

end NCConcave16991.BranchOracle
