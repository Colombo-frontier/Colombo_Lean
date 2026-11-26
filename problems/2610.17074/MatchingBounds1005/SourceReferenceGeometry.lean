import MatchingBounds1005.AnalyticReferenceParameters
import MatchingBounds1005.SourceReferenceCalendar
import MatchingBounds1005.ScheduledPrefixDimension
import MatchingBounds1005.FinalScalarCalibration

/-! The actual accessible reference program satisfies the full scheduled
Haar prefix bound. Its entire private Gaussian seed is independent of the
single Haar rotation; the public schedule and start count are derived. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration PathGreen BlockGeometry PathLayers GaussianVector
open ScheduledHaar ScheduledPrefix SourceReferenceProgram FiniteGaussianSampler

theorem referenceParameters_Q_eq (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) :
    (referenceParameters p t ht hs (powerCopies t)).Q = canonicalOperator p t ht hs := by
  rfl

theorem referenceLayer_le_active (p : ℕ) (t : ℝ) (j : ℕ) :
    referenceLayer p t (powerCopies t) j ≤ canonicalActive p t :=
  ambientLayerSpace_le_active _ _ _ _ _

theorem referenceParameters_b_active (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p)
    (i : Fin (phaseCount (amplitudeConstant p) t - 1 + 1)) :
    (referenceParameters p t ht hs (powerCopies t)).b i ∈ canonicalActive p t :=
  normalized_ambientReadout_mem_active _ _ _ _ i

def referenceCommandSpace (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (H : ℕ) (j : ℕ) :
    Submodule ℝ (Vec (dimension p t (powerCopies t))) :=
  referenceLayer p t (powerCopies t)
    (commandClock (commands (referenceParameters p t ht hs (powerCopies t)) H) 1 j)

theorem referenceCommandSpace_mono (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (H j : ℕ) :
    referenceCommandSpace p t ht hs H j ≤ referenceCommandSpace p t ht hs H (j + 1) :=
  calendar_spaces_mono _ 1 _ (fun q => referenceLayer_mono p t _ (Nat.le_succ q)) j

theorem referenceCommandSpace_le_active (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (H j : ℕ) :
    referenceCommandSpace p t ht hs H j ≤ canonicalActive p t :=
  referenceLayer_le_active p t _

theorem reference_start_count (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (H : ℕ) (hH : H ≤ baseSize p t) :
    let w := commands (referenceParameters p t ht hs (powerCopies t)) H
    actionCount w.length + actionCount w.length ≤ maximalStarts p t := by
  have hphase := phase_pos p ht hs
  have hN := readout_count_le_baseSize p t ht hs
  exact bounded_start_count _ H (baseSize p t) (by omega) hH

theorem reference_dimension_room (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (hg : t ≤ geometryThreshold p)
    (H : ℕ) (hH : H ≤ baseSize p t) :
    actionCount (commands (referenceParameters p t ht hs (powerCopies t)) H).length ≤
      dimension p t (powerCopies t) := by
  have hc := reference_start_count p t ht hs H hH
  have hd := source_dimension_room p t ht hg _ hc
  omega

variable {Seed : Type} [MeasurableSpace Seed]

theorem reference_plan_scheduled (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (H : ℕ)
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed) :
    let P := referenceParameters p t ht hs (powerCopies t)
    (plan (H := H) P A).Scheduled P.Q (commands P H) (referenceCommandSpace p t ht hs H) :=
  plan_scheduled _ A _ (referenceParameters_c_initial p t ht hs _)
    (referenceParameters_b_disclosed p t ht hs _) (referenceParameters_Q_propagation p t ht hs _)

def referenceFullTrace (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (H : ℕ)
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed)
    (z : (Seed × Noise (TensorChannelRows.jointDim (dimension p t (powerCopies t))) H) ×
      Rotation (Vec (dimension p t (powerCopies t)))) :
    Fin (commands (referenceParameters p t ht hs (powerCopies t)) H).length →
      Vec (dimension p t (powerCopies t)) :=
  let P := referenceParameters p t ht hs (powerCopies t)
  let w := commands P H
  roundQueryTrace _ w.length (((plan P A).compile w).run w.length P.Q
    (z.2 : Vec (dimension p t (powerCopies t)) →L[ℝ] Vec (dimension p t (powerCopies t))) z.1)

def referenceFullPrefixGood (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (H : ℕ)
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed) :
    Set ((Seed × Noise (TensorChannelRows.jointDim (dimension p t (powerCopies t))) H) ×
      Rotation (Vec (dimension p t (powerCopies t)))) :=
  {z | referenceFullTrace p t ht hs H A z ∈
    prefixEvent (referenceCommandSpace p t ht hs H) (canonicalActive p t) (sourceAngle p t)}

theorem referenceFullPrefixGood_measurable (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (hg : t ≤ geometryThreshold p)
    (H : ℕ) (hH : H ≤ baseSize p t)
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed) :
    MeasurableSet (referenceFullPrefixGood p t ht hs H A) :=
  RoundPolicy.haar_prefix_measurable _ (reference_dimension_room p t ht hs hg H hH) _
    ((plan _ A).compile _) _ _ _

/-- No algorithm-dependent angle hypothesis remains: the copied path-chain
operator, schedule, Gaussian starts, and ambient dimension are all actual. -/
theorem reference_full_prefix_failure (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (hg : t ≤ geometryThreshold p)
    (H : ℕ) (hH : H ≤ baseSize p t) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed) :
    ((ν.prod (noiseLaw (TensorChannelRows.jointDim (dimension p t (powerCopies t))) H)).prod
      (haarLaw (Vec (dimension p t (powerCopies t))))).real
        (referenceFullPrefixGood p t ht hs H A)ᶜ ≤ 1 / (powerCopies t : ℝ) ^ 4 := by
  let P := referenceParameters p t ht hs (powerCopies t)
  let w := commands P H
  have hc := reference_start_count p t ht hs H hH
  have hangle := source_cyclic_angle_failure p t ht hg _ hc
  have hangle' : (GaussianMatrix.gaussianMatrixLaw (dimension p t (powerCopies t))
      (actionCount w.length + actionCount w.length)).real
      {g | ¬ GaussianBlockGeometry.CyclicAngleGood (canonicalActive p t) P.Q g (sourceAngle p t)} ≤
        1 / (powerCopies t : ℝ) ^ 4 := by
    simpa only [P, referenceParameters_Q_eq] using hangle
  exact SourcePolicy.haar_prefix_failure_of_dimension w (dimension_pos p t ht hs _)
    (reference_dimension_room p t ht hs hg H hH)
    (ν.prod (noiseLaw (TensorChannelRows.jointDim (dimension p t (powerCopies t))) H))
    P.Q (plan P A) (referenceCommandSpace p t ht hs H) (canonicalActive p t)
    (referenceCommandSpace_mono p t ht hs H) (reference_plan_scheduled p t ht hs H A)
    (referenceCommandSpace_le_active p t ht hs H) (geometricAngle_nonneg _ _ _)
    (sourceAngle_half p t ht hg) hangle'

/-- The final calibrated query budget has the source K⁻⁴ reference failure
probability, uniformly over arbitrary measurable algorithms and seed laws. -/
theorem source_reference_prefix_failure (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ lowerThreshold p) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed) :
    let hs := hsmall.trans (lowerThreshold_le_parameter p)
    let H := candidateBudget p t
    ((ν.prod (noiseLaw (TensorChannelRows.jointDim (dimension p t (powerCopies t))) H)).prod
      (haarLaw (Vec (dimension p t (powerCopies t))))).real
        (referenceFullPrefixGood p t ht hs H A)ᶜ ≤ 1 / (powerCopies t : ℝ) ^ 4 :=
  reference_full_prefix_failure p t ht (hsmall.trans (lowerThreshold_le_parameter p))
    (hsmall.trans (lowerThreshold_le_geometry p)) (candidateBudget p t)
    (candidateBudget_le_baseSize p t ht (hsmall.trans (lowerThreshold_le_candidate p))) ν A

end MatchingBounds1005.AnalyticFamily
