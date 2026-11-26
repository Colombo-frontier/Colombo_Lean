import MatchingBounds1005.SourceKLEstimate
import MatchingBounds1005.AnalyticEntropyBound
import MatchingBounds1005.AnalyticReferenceFailure

/-! The unconditional adaptive comparison for the calibrated construction.
All geometric, posterior, row-space, and integrability assumptions are discharged. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations InformationTheory
open scoped ENNReal
namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration TensorGeometry SourceReferenceReplay CensoredGaussianProcess

theorem actual_comparison_kl_le {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ lowerThreshold p)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed) :
    let hs := hsmall.trans (lowerThreshold_le_parameter p)
    let P := referenceParameters p t ht hs (powerCopies t)
    let μ := (haarLaw (Vec (dimension p t (powerCopies t)))).prod ν
    klDiv (referenceLaw (sourceProtocol (H := candidateBudget p t) P A) 1 μ (candidateBudget p t))
      (trueLaw (sourceProtocol (H := candidateBudget p t) P A) 1 μ (candidateBudget p t)) ≤
        ENNReal.ofReal (sourceInformationBudget p t ht hs) := by
  dsimp only
  let hs := hsmall.trans (lowerThreshold_le_parameter p)
  let P := referenceParameters p t ht hs (powerCopies t)
  have hb := referenceParameters_readouts_orthonormal p t ht hs (powerCopies t)
  have he := source_klDiv_le (θ := 2 * sourceAngle p t) P A
    (referenceParameters_disclosure_pos p t ht hs (powerCopies t)) (fun i => hb.norm_eq_one i)
    ((haarLaw (Vec (dimension p t (powerCopies t)))).prod ν)
    (mul_nonneg (by norm_num) (geometricAngle_nonneg _ _ _)) (1 / (powerCopies t : ℝ) ^ 4)
    (actual_reference_bad_le p t ht hsmall ν A)
  dsimp only [P] at he
  rw [actual_pairCost_budget p t ht hs] at he
  exact he

end MatchingBounds1005.AnalyticFamily
