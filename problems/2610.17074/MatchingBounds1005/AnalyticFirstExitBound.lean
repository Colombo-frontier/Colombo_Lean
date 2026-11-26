import MatchingBounds1005.AnalyticTrueTrace
import MatchingBounds1005.AnalyticReferenceFailure
import MatchingBounds1005.AnalyticEntropyBound
import MatchingBounds1005.AnalyticHardness

/-! The original fixed objective family's first-exit probability, for every
measurable algorithm and every independent private seed law. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations
namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration TensorGeometry SourceReferenceProgram SourceReferenceReplay CensoredGaussianProcess

theorem actual_firstExit_le {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ lowerThreshold p)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed) :
    let hs := hsmall.trans (lowerThreshold_le_parameter p)
    ((sampleLaw p t (powerCopies t)).prod ν).real
      (firstExitEvent p t ht hs (powerCopies t) A (disclosedSet p t ht hs (powerCopies t))
        (candidateBudget p t)) ≤ 1 / 15 := by
  dsimp only
  let hs := hsmall.trans (lowerThreshold_le_parameter p)
  let K := powerCopies t
  let H := candidateBudget p t
  let P := referenceParameters p t ht hs K
  let G := queryGeometryEvent p t ht hs K H A
  have hG : MeasurableSet G := queryGeometryEvent_measurable p t ht hs K H A
  have hsubset : firstExitEvent p t ht hs K A (disclosedSet p t ht hs K) H ⊆
      sampledTrace p t ht hs K H A ⁻¹' Gᶜ := by
    intro z hz
    have he := (firstExit_iff_traceExitEvent p t ht hs K A (disclosedSet p t ht hs K) H z.1 z.2).mp hz
    intro hg
    exact geometryEvent_no_exit p t ht hs (hsmall.trans (lowerThreshold_le_geometry p)) K H
      (candidateBudget_safe p t ht (hsmall.trans (lowerThreshold_le_candidate p))) A
      (sampledTrace p t ht hs K H A z) hg he
  have hmap := congrArg (fun μ => μ Gᶜ) (sampledTrace_law p t ht hs K H A ν)
  dsimp only at hmap
  rw [Measure.map_apply (sampledTrace_measurable p t ht hs K H A) hG.compl,
    Measure.map_apply (trace_measurable P A (rotationMap _)
      (fun i => rotationMap_column_measurable (P.b i)) (rotationMap_column_measurable P.c)
      (rotationMap_quadratic_measurable P.Q) H) hG.compl] at hmap
  have hreal : (((sampleLaw p t K).prod ν).real (sampledTrace p t ht hs K H A ⁻¹' Gᶜ)) =
      (trueLaw (sourceProtocol P A) 1 ((haarLaw (Vec (dimension p t K))).prod ν) H).real
        (traceGood P A (2 * sourceAngle p t))ᶜ := by
    simpa only [Measure.real, G, queryGeometryEvent, stoppedReadout, traceGood, Set.preimage_compl]
      using congrArg ENNReal.toReal hmap
  have hb := actual_true_bad_le p t ht hsmall ν A (actual_reference_bad_le p t ht hsmall ν A)
  apply (measureReal_mono hsubset).trans
  rw [hreal]
  exact hb

theorem actual_hardDistribution (p : ℕ) (hp : 1 ≤ p) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ lowerThreshold p) :
    Model.HardDistribution p (dimension p t (powerCopies t)) (candidateBudget p t) (t ^ 3) := by
  let hs := hsmall.trans (lowerThreshold_le_parameter p)
  apply conditioned_hardDistribution_of_firstExit p hp t ht hs (powerCopies t) (candidateBudget p t)
    (disclosedSet p t ht hs (powerCopies t))
  intro Seed _ _ ν _ A
  exact actual_firstExit_le p t ht hsmall ν A

end MatchingBounds1005.AnalyticFamily
