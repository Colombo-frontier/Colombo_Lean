import MatchingBounds1005.AnalyticOracle
import MatchingBounds1005.FirstExitTrace

/-! The concrete first-exit event is measurable in (rotation, private policy
seed, finite oracle history) and does not inspect the static Gaussian mask.
It is therefore the same event for true and reference transcript laws. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration TensorGeometry

theorem sourceReadout_rotation_continuous (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ)
    (i : Fin (phaseCount (amplitudeConstant p) t - 1 + 1)) :
    Continuous (fun U : Rotation (Vec (dimension p t K)) =>
      sourceReadouts p t ht hs K (rotationIso p t K U) i) := by
  change Continuous (fun U : Rotation (Vec (dimension p t K)) =>
    isometry _ U (sourceReadouts p t ht hs K (coordinateIso p t K) i))
  exact (continuous_action _).comp (continuous_id.prodMk continuous_const)

theorem tail_rotation_continuous (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ) :
    Continuous (fun U : Rotation (Vec (dimension p t K)) =>
      tail p t ht hs K (rotationIso p t K U)) := by
  change Continuous (fun U : Rotation (Vec (dimension p t K)) =>
    isometry _ U (tail p t ht hs K (coordinateIso p t K)))
  exact (continuous_action _).comp (continuous_id.prodMk continuous_const)

def rotationQuerySafe {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (A : Model.Algorithm (dimension p t K) Seed)
    (S : ℕ → Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1)))
    (j : ℕ) (z : Rotation (Vec (dimension p t K)) × Seed)
    (h : Fin j → Model.Response (dimension p t K)) : Prop :=
  ∀ i, i ∉ S j → |⟪sourceReadouts p t ht hs K (rotationIso p t K z.1) i,
    radial (t ^ 3)⁻¹ (A.query j z.2 h)⟫_ℝ| ≤ 1

def rotationOutputSafe {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (A : Model.Algorithm (dimension p t K) Seed) (T : ℕ)
    (z : Rotation (Vec (dimension p t K)) × Seed)
    (h : Fin T → Model.Response (dimension p t K)) : Prop :=
  |⟪tail p t ht hs K (rotationIso p t K z.1), radial (t ^ 3)⁻¹ (A.output T z.2 h)⟫_ℝ| ≤
    16 * t ^ 3 / RadialHigher.baseBudget p

theorem rotationQuerySafe_measurable {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (A : Model.Algorithm (dimension p t K) Seed)
    (S : ℕ → Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1))) (j : ℕ) :
    MeasurableSet {z : (Rotation (Vec (dimension p t K)) × Seed) ×
      (Fin j → Model.Response (dimension p t K)) | rotationQuerySafe p t ht hs K A S j z.1 z.2} := by
  classical
  simp only [rotationQuerySafe, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  have hq : Measurable (fun z : (Rotation (Vec (dimension p t K)) × Seed) ×
      (Fin j → Model.Response (dimension p t K)) => A.query j z.1.2 z.2) :=
    (A.query_measurable j).comp (measurable_fst.snd.prodMk measurable_snd)
  have hr := (radial_contDiff (E := Vec (dimension p t K)) (t ^ 3)⁻¹ ∞).continuous.measurable.comp hq
  have hb : Measurable (fun z : (Rotation (Vec (dimension p t K)) × Seed) ×
      (Fin j → Model.Response (dimension p t K)) =>
      sourceReadouts p t ht hs K (rotationIso p t K z.1.1) i) :=
    (sourceReadout_rotation_continuous p t ht hs K i).measurable.comp measurable_fst.fst
  exact measurableSet_le (hb.inner hr).abs measurable_const

theorem rotationOutputSafe_measurable {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (A : Model.Algorithm (dimension p t K) Seed) (T : ℕ) :
    MeasurableSet {z : (Rotation (Vec (dimension p t K)) × Seed) ×
      (Fin T → Model.Response (dimension p t K)) | rotationOutputSafe p t ht hs K A T z.1 z.2} := by
  have hq : Measurable (fun z : (Rotation (Vec (dimension p t K)) × Seed) ×
      (Fin T → Model.Response (dimension p t K)) => A.output T z.1.2 z.2) :=
    (A.output_measurable T).comp (measurable_fst.snd.prodMk measurable_snd)
  have hr := (radial_contDiff (E := Vec (dimension p t K)) (t ^ 3)⁻¹ ∞).continuous.measurable.comp hq
  have hb : Measurable (fun z : (Rotation (Vec (dimension p t K)) × Seed) ×
      (Fin T → Model.Response (dimension p t K)) => tail p t ht hs K (rotationIso p t K z.1.1)) :=
    (tail_rotation_continuous p t ht hs K).measurable.comp measurable_fst.fst
  exact measurableSet_le (hb.inner hr).abs measurable_const

def traceExitEvent {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (A : Model.Algorithm (dimension p t K) Seed)
    (S : ℕ → Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1))) (T : ℕ) :=
  Model.TraceExit (rotationQuerySafe p t ht hs K A S) (rotationOutputSafe p t ht hs K A T)

theorem traceExitEvent_measurable {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (A : Model.Algorithm (dimension p t K) Seed)
    (S : ℕ → Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1))) (T : ℕ) :
    MeasurableSet (traceExitEvent p t ht hs K A S T) :=
  Model.traceExit_measurable _ _ (rotationQuerySafe_measurable p t ht hs K A S)
    (rotationOutputSafe_measurable p t ht hs K A T)

theorem firstExit_iff_traceExitEvent {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (A : Model.Algorithm (dimension p t K) Seed)
    (S : ℕ → Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1))) (T : ℕ)
    (z : Sample p t K) (seed : Seed) :
    seed ∈ Model.FirstExit (sampledReply p t ht hs K z A S)
      (querySafe p t ht hs K z A S) (outputSafe p t ht hs K z A T) ↔
    ((z.1, seed), Model.replyTranscript (sampledReply p t ht hs K z A S) seed T) ∈
      traceExitEvent p t ht hs K A S T := by
  rw [Model.firstExit_iff_traceExit]
  rfl

end MatchingBounds1005.AnalyticFamily
