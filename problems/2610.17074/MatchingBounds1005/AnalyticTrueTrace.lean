import MatchingBounds1005.SourceStaticLaw
import MatchingBounds1005.SourceTraceEnergy
import MatchingBounds1005.AnalyticStaticResponse
import MatchingBounds1005.AnalyticGeometryEvent
import MatchingBounds1005.GaussianSeedRepacking

/-! Exact reconstructed transcript law under one fixed Haar rotation and two fixed
Gaussian masks. These are the `sampledReply` responses; equality with the objective
oracle is supplied separately up to the first exit by `AnalyticOracle`. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration TensorGeometry SourceReferenceProgram SourceReferenceReplay
open TensorChannelRows GaussianSeedRepacking CensoredGaussianProcess

variable {Seed : Type} [MeasurableSpace Seed]

def sampledTrace (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K H : ℕ) (A : Model.Algorithm (dimension p t K) Seed) (z : Sample p t K × Seed) :
    (Rotation (Vec (dimension p t K)) × Seed) × (Fin H → Model.Response (dimension p t K)) :=
  ((z.1.1, z.2), Model.replyTranscript
    (sampledReply p t ht hs K z.1 A (disclosedSet p t ht hs K)) z.2 H)

theorem directTrace_repack (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K H : ℕ) (A : Model.Algorithm (dimension p t K) Seed)
    (z : (Rotation (Vec (dimension p t K)) × Seed) × Vec (jointDim (dimension p t K))) :
    directTrace (referenceParameters p t ht hs K) A (rotationMap _) H z =
      sampledTrace p t ht hs K H A (repack (cubicDim _) (quarticDim _) z) := by
  unfold directTrace sampledTrace
  dsimp only [repack]
  apply congrArg (fun h => (z.1, h))
  apply congrArg (fun reply => Model.replyTranscript reply z.1.2 H)
  funext j seed h
  exact directResponse_eq_sourceReply p t ht hs K z.1.1 z.2 j (A.query j seed h)

theorem sampledTrace_measurable (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K H : ℕ) (A : Model.Algorithm (dimension p t K) Seed) :
    Measurable (sampledTrace p t ht hs K H A) := by
  let P := referenceParameters p t ht hs K
  have hd : Measurable (directTrace P A (rotationMap _) H) :=
    directTrace_measurable (H := H) P A (rotationMap _)
      (fun i => rotationMap_column_measurable (P.b i))
      (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q)
      (referenceParameters_disclosure_pos p t ht hs K) (referenceParameters_core p t ht hs K)
      (referenceParameters_sigmas_pos p t ht hs K).1.ne'
      (referenceParameters_sigmas_pos p t ht hs K).2.ne'
  have heq : sampledTrace p t ht hs K H A =
      fun z => directTrace P A (rotationMap _) H (unpack (cubicDim _) (quarticDim _) z) := by
    funext z
    have h := directTrace_repack p t ht hs K H A (unpack (cubicDim _) (quarticDim _) z)
    rw [repack_unpack] at h
    exact h.symm
  rw [heq]
  exact hd.comp (unpack_measurable _ _)

/-- The true-law KL comparison is attached to the reconstructed replies under
the article's fixed rotation and independent fixed masks, with the original
algorithm seed. This is not a global equality with the objective oracle. -/
theorem sampledTrace_law (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K H : ℕ) (A : Model.Algorithm (dimension p t K) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ((sampleLaw p t K).prod ν).map (sampledTrace p t ht hs K H A) =
      (trueLaw (sourceProtocol (H := H) (referenceParameters p t ht hs K) A) 1
        ((haarLaw (Vec (dimension p t K))).prod ν) H).map
          (trace (H := H) (referenceParameters p t ht hs K) A (rotationMap _) H) := by
  let P := referenceParameters p t ht hs K
  rw [← analytic_seed_repack_map p t K ν]
  rw [Measure.map_map (sampledTrace_measurable p t ht hs K H A)
    (repack_measurable (Rot := Rotation (Vec (dimension p t K))) (Seed := Seed)
      (cubicDim (dimension p t K)) (quarticDim (dimension p t K)))]
  calc
    _ = (((haarLaw (Vec (dimension p t K))).prod ν).prod
        (GaussianVector.standardGaussian (jointDim (dimension p t K)))).map
          (directTrace P A (rotationMap _) H) := by
      congr 1
      funext z
      exact (directTrace_repack p t ht hs K H A z).symm
    _ = _ := (true_trace_law (H := H) P A (rotationMap _)
      (fun i => rotationMap_column_measurable (P.b i))
      (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q)
      (referenceParameters_disclosure_pos p t ht hs K) (referenceParameters_core p t ht hs K)
      (referenceParameters_sigmas_pos p t ht hs K).1.ne'
      (referenceParameters_sigmas_pos p t ht hs K).2.ne'
      (haarLaw (Vec (dimension p t K))) ν).symm

end MatchingBounds1005.AnalyticFamily

