import MatchingBounds1005.SourceEntropyTransfer
import MatchingBounds1005.AnalyticReferenceRotation
import MatchingBounds1005.FinalScalarCalibration

/-! Exact identification of the implemented source protocol's energy budget
with the calibrated scalar budget, and the resulting 1/15 bad-event bound. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations
namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration TensorGeometry SourceReferenceReplay CensoredGaussianProcess

theorem actual_pairCost_budget (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) :
    pairCostCap (referenceParameters p t ht hs (powerCopies t)) (2 * sourceAngle p t) +
      (1 / (powerCopies t : ℝ) ^ 4) * pairCostCap (referenceParameters p t ht hs (powerCopies t)) 1 =
        sourceInformationBudget p t ht hs := by
  simp only [pairCostCap, referenceParameters, sourceInformationBudget, tensorEnergyBudget,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.sub_add_cancel (phase_pos p ht hs)]
  rfl

theorem actual_true_bad_le {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ lowerThreshold p)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed)
    (hfail : let hs := hsmall.trans (lowerThreshold_le_parameter p)
      let P := referenceParameters p t ht hs (powerCopies t)
      (referenceLaw (sourceProtocol P A) 1 ((haarLaw (Vec (dimension p t (powerCopies t)))).prod ν)
        (candidateBudget p t)).real (traceGood P A (2 * sourceAngle p t))ᶜ ≤ 1 / (powerCopies t : ℝ) ^ 4) :
    let hs := hsmall.trans (lowerThreshold_le_parameter p)
    let P := referenceParameters p t ht hs (powerCopies t)
    (trueLaw (sourceProtocol P A) 1 ((haarLaw (Vec (dimension p t (powerCopies t)))).prod ν)
      (candidateBudget p t)).real (traceGood P A (2 * sourceAngle p t))ᶜ ≤ 1 / 15 := by
  dsimp only at hfail ⊢
  let hs := hsmall.trans (lowerThreshold_le_parameter p)
  let P := referenceParameters p t ht hs (powerCopies t)
  have hb := referenceParameters_readouts_orthonormal p t ht hs (powerCopies t)
  have he := source_true_bad_probability (θ := 2 * sourceAngle p t) P A
    (referenceParameters_disclosure_pos p t ht hs (powerCopies t)) (fun i => hb.norm_eq_one i)
    ((haarLaw (Vec (dimension p t (powerCopies t)))).prod ν)
    (mul_nonneg (by norm_num) (geometricAngle_nonneg _ _ _)) (1 / (powerCopies t : ℝ) ^ 4) hfail
  dsimp only [P] at he
  rw [actual_pairCost_budget p t ht hs] at he
  exact he.trans (final_entropy_transfer_bound p t ht hsmall)

end MatchingBounds1005.AnalyticFamily
