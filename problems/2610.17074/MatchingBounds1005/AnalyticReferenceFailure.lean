import MatchingBounds1005.SourceReferenceGeometry
import MatchingBounds1005.SourceReferenceTraceGeometry
import MatchingBounds1005.ReadoutPrefixCompression
import MatchingBounds1005.SourceTraceEnergy

/-! The actual censored Gaussian reference law inherits the source K⁻⁴
geometry failure bound. The complete analyst event is compressed, the
private Gaussian seed is forgotten, and the exact transcript law is used. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration GaussianVector ScheduledHaar ScheduledPrefix
open SourceReferenceProgram SourceReferenceReplay FiniteGaussianSampler
open CensoredGaussianProcess
variable {Seed : Type} [MeasurableSpace Seed]

theorem program_geometry_good_of_full_prefix (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (H : ℕ)
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed)
    (z : (Seed × Noise (TensorChannelRows.jointDim (dimension p t (powerCopies t))) H) ×
      Rotation (Vec (dimension p t (powerCopies t))))
    (hz : z ∈ referenceFullPrefixGood p t ht hs H A) :
    let P := referenceParameters p t ht hs (powerCopies t)
    programTrace P A (rotationMap _) (z.2, z.1) ∈
      Model.geometryEvent P.R A H P.b (stoppedPrefixLength P H) (2 * sourceAngle p t) := by
  let P := referenceParameters p t ht hs (powerCopies t)
  have hc := readoutEvent_of_full_prefix P H (referenceFullTrace p t ht hs H A z)
    (referenceLayer p t (powerCopies t)) (canonicalActive p t)
    (referenceParameters_b_active p t ht hs)
    (fun s j hj => referenceParameters_b_hidden p t ht hs _ j s hj) hz
  have he := planTrace_compressed P A (rotationMap _)
    (fun i => rotationMap_column_measurable (P.b i))
    (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q)
    (z.2, z.1.1) z.1.2
  have he' : (fun i => referenceFullTrace p t ht hs H A z (observationIndex P H i)) =
      Model.canonicalQueryTrace P.R A H (programTrace P A (rotationMap _) (z.2, z.1)) := by
    simpa only [referenceFullTrace, Model.canonicalQueryTrace, programTrace, rotationMap,
      LinearIsometryEquiv.adjoint_eq_symm] using he
  rw [he'] at hc
  exact hc

/-- The reference law here is exactly the Gaussian law used by the KL
comparison; no separate random-subspace or abstract reference-law premise
is assumed. -/
theorem reference_geometry_failure (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (hg : t ≤ geometryThreshold p)
    (H : ℕ) (hH : H ≤ baseSize p t) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed) :
    let P := referenceParameters p t ht hs (powerCopies t)
    (referenceLaw (sourceProtocol (H := H) P A) 1
      ((haarLaw (Vec (dimension p t (powerCopies t)))).prod ν) H).real
        (traceGood (H := H) P A (2 * sourceAngle p t))ᶜ ≤ 1 / (powerCopies t : ℝ) ^ 4 := by
  let P := referenceParameters p t ht hs (powerCopies t)
  let νR := haarLaw (Vec (dimension p t (powerCopies t)))
  let νprivate := ν.prod (noiseLaw (TensorChannelRows.jointDim (dimension p t (powerCopies t))) H)
  let event := Model.geometryEvent P.R A H P.b (stoppedPrefixLength P H) (2 * sourceAngle p t)
  have hevent : MeasurableSet event := Model.geometryEvent_measurable _ _ _ _ _ _
  have hprog := programTrace_measurable (H := H) P A (rotationMap _)
    (fun i => rotationMap_column_measurable (P.b i))
    (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q)
  have htrace := trace_measurable (H := H) P A (rotationMap _)
    (fun i => rotationMap_column_measurable (P.b i))
    (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q) H
  have hlaw := programTrace_law (H := H) P A (rotationMap _)
    (fun i => rotationMap_column_measurable (P.b i))
    (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q) νR ν
  have heq := congrArg (fun μ => μ.real eventᶜ) hlaw
  dsimp only at heq
  rw [map_measureReal_apply hprog hevent.compl, map_measureReal_apply htrace hevent.compl] at heq
  have hsub : programTrace (H := H) P A (rotationMap _) ⁻¹' eventᶜ ⊆
      Prod.swap ⁻¹' (referenceFullPrefixGood p t ht hs H A)ᶜ := by
    intro z hz hfull
    exact hz (program_geometry_good_of_full_prefix p t ht hs H A z.swap hfull)
  have hgood := referenceFullPrefixGood_measurable p t ht hs hg H hH A
  have hswap := (Measure.measurePreserving_swap (μ := νR) (ν := νprivate)).measureReal_preimage
    hgood.compl.nullMeasurableSet
  calc
    _ = (νR.prod νprivate).real (programTrace P A (rotationMap _) ⁻¹' eventᶜ) := heq.symm
    _ ≤ (νR.prod νprivate).real (Prod.swap ⁻¹' (referenceFullPrefixGood p t ht hs H A)ᶜ) :=
      measureReal_mono hsub
    _ = (νprivate.prod νR).real (referenceFullPrefixGood p t ht hs H A)ᶜ := hswap
    _ ≤ _ := reference_full_prefix_failure p t ht hs hg H hH ν A

theorem actual_reference_bad_le (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ lowerThreshold p) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Model.Algorithm (dimension p t (powerCopies t)) Seed) :
    let hs := hsmall.trans (lowerThreshold_le_parameter p)
    let P := referenceParameters p t ht hs (powerCopies t)
    let H := candidateBudget p t
    (referenceLaw (sourceProtocol (H := H) P A) 1
      ((haarLaw (Vec (dimension p t (powerCopies t)))).prod ν) H).real
        (traceGood (H := H) P A (2 * sourceAngle p t))ᶜ ≤ 1 / (powerCopies t : ℝ) ^ 4 :=
  reference_geometry_failure p t ht (hsmall.trans (lowerThreshold_le_parameter p))
    (hsmall.trans (lowerThreshold_le_geometry p)) (candidateBudget p t)
    (candidateBudget_le_baseSize p t ht (hsmall.trans (lowerThreshold_le_candidate p))) ν A

end MatchingBounds1005.AnalyticFamily
