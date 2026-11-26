import MinimaxAudit.RandomizedOracle
import MinimaxAudit.MeasurableExecution

/-!
The actual source scalar policy supplies adapted Haar probes. All measurability,
prefix adaptation and feasible-radius facts below are proved from the policy's
canonical sigma algebra and the differentiated scalar truncated oracle.
-/
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace MinimaxAudit.Randomized
open VIReference.Pilot VIReference.Pilot.BorelStoppingPolicy
open MeasurableExecution

noncomputable section
variable {N d p : ℕ} {R tau : ℝ} {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}

abbrev BallPolicy (p d N : ℕ) (R : ℝ) (Seed : Type*) [MeasurableSpace Seed] (mu : Measure Seed) :=
  RandomizedScalarPolicy p d d N (Metric.closedBall 0 R) (Metric.closedBall 0 R) Seed mu

abbrev BallFeasible (d : ℕ) (R : ℝ) :=
  productDomain (Metric.closedBall (0 : Primal d) R) (Metric.closedBall (0 : Dual d) R)

theorem sourceHaarQuery_primal_jointlyMeasurable
    (hnd : N + 1 < d) (A : BallPolicy p d N R Seed mu) (fill : BallFeasible d R)
    (profile : GateProfile) (htau : tau ≠ 0) (lam c q : ℝ) (t : Fin N) :
    Measurable (fun w : (Haar.FrameSample d × Haar.FrameSample d) × Seed =>
      primalBlock (scalarRunnerQuery A fill
        (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) t w)) := by
  have hr := (scalar_runner_jointly_measurable A fill
    (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p)
    (scalarHaarStage_jointlyMeasurable (Nat.le_of_lt hnd) profile htau lam c q p)).1 t
  simpa only [Function.comp_def, primal_projection_apply] using (primalProjection d d).measurable.comp hr

theorem sourceHaarQuery_dual_jointlyMeasurable
    (hnd : N + 1 < d) (A : BallPolicy p d N R Seed mu) (fill : BallFeasible d R)
    (profile : GateProfile) (htau : tau ≠ 0) (lam c q : ℝ) (t : Fin N) :
    Measurable (fun w : (Haar.FrameSample d × Haar.FrameSample d) × Seed =>
      dualBlock (scalarRunnerQuery A fill
        (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) t w)) := by
  have hr := (scalar_runner_jointly_measurable A fill
    (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p)
    (scalarHaarStage_jointlyMeasurable (Nat.le_of_lt hnd) profile htau lam c q p)).1 t
  simpa only [Function.comp_def, dual_projection_apply] using (dualProjection d d).measurable.comp hr

theorem sourceHaarOutput_primal_jointlyMeasurable
    (hnd : N + 1 < d) (A : BallPolicy p d N R Seed mu) (fill : BallFeasible d R)
    (profile : GateProfile) (htau : tau ≠ 0) (lam c q : ℝ) :
    Measurable (fun w : (Haar.FrameSample d × Haar.FrameSample d) × Seed =>
      primalBlock (scalarRunnerOutput A fill
        (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) w)) := by
  have hr := (scalar_runner_jointly_measurable A fill
    (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p)
    (scalarHaarStage_jointlyMeasurable (Nat.le_of_lt hnd) profile htau lam c q p)).2
  simpa only [Function.comp_def, primal_projection_apply] using (primalProjection d d).measurable.comp hr

theorem sourceHaarOutput_dual_jointlyMeasurable
    (hnd : N + 1 < d) (A : BallPolicy p d N R Seed mu) (fill : BallFeasible d R)
    (profile : GateProfile) (htau : tau ≠ 0) (lam c q : ℝ) :
    Measurable (fun w : (Haar.FrameSample d × Haar.FrameSample d) × Seed =>
      dualBlock (scalarRunnerOutput A fill
        (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) w)) := by
  have hr := (scalar_runner_jointly_measurable A fill
    (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p)
    (scalarHaarStage_jointlyMeasurable (Nat.le_of_lt hnd) profile htau lam c q p)).2
  simpa only [Function.comp_def, dual_projection_apply] using (dualProjection d d).measurable.comp hr

/-- The actual scalar virtual execution, for a fixed independent seed,
satisfies every adapted-probe assumption of the concrete Haar lemma. -/
def sourceHaarProbes
    (hnd : N + 1 < d) (A : BallPolicy p d N R Seed mu) (fill : BallFeasible d R)
    (profile : GateProfile) (htau : tau ≠ 0) (lam c q : ℝ) (seed : Seed) :
    Haar.PairedProbeFamily N d R hnd where
  primalQuery t Q := primalBlock (scalarRunnerQuery A fill
    (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) t (Q, seed))
  dualQuery t Q := dualBlock (scalarRunnerQuery A fill
    (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) t (Q, seed))
  primalOutput Q := primalBlock (scalarRunnerOutput A fill
    (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) (Q, seed))
  dualOutput Q := dualBlock (scalarRunnerOutput A fill
    (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) (Q, seed))
  primalQuery_meas t i := by
    have hframe : Measurable (fun Q : Haar.FrameSample d × Haar.FrameSample d =>
        haarStiefelFrame (Nat.le_of_lt hnd) Q.1 i) :=
      ((measurable_pi_apply i).comp (measurable_haarStiefelFrame (Nat.le_of_lt hnd))).comp measurable_fst
    exact hframe.inner (𝕜 := ℝ) ((sourceHaarQuery_primal_jointlyMeasurable hnd A fill profile htau lam c q t).comp
      (measurable_id.prodMk measurable_const))
  dualQuery_meas t i := by
    have hframe : Measurable (fun Q : Haar.FrameSample d × Haar.FrameSample d =>
        haarStiefelFrame (Nat.le_of_lt hnd) Q.2 i) :=
      ((measurable_pi_apply i).comp (measurable_haarStiefelFrame (Nat.le_of_lt hnd))).comp measurable_snd
    exact hframe.inner (𝕜 := ℝ) ((sourceHaarQuery_dual_jointlyMeasurable hnd A fill profile htau lam c q t).comp
      (measurable_id.prodMk measurable_const))
  primalOutput_meas := by
    have hframe : Measurable (fun Q : Haar.FrameSample d × Haar.FrameSample d =>
        haarStiefelFrame (Nat.le_of_lt hnd) Q.1 (Fin.last N)) :=
      ((measurable_pi_apply (Fin.last N)).comp (measurable_haarStiefelFrame (Nat.le_of_lt hnd))).comp measurable_fst
    exact hframe.inner (𝕜 := ℝ) ((sourceHaarOutput_primal_jointlyMeasurable hnd A fill profile htau lam c q).comp
      (measurable_id.prodMk measurable_const))
  dualOutput_meas := by
    have hframe : Measurable (fun Q : Haar.FrameSample d × Haar.FrameSample d =>
        haarStiefelFrame (Nat.le_of_lt hnd) Q.2 (Fin.last N)) :=
      ((measurable_pi_apply (Fin.last N)).comp (measurable_haarStiefelFrame (Nat.le_of_lt hnd))).comp measurable_snd
    exact hframe.inner (𝕜 := ℝ) ((sourceHaarOutput_dual_jointlyMeasurable hnd A fill profile htau lam c q).comp
      (measurable_id.prodMk measurable_const))
  primalQuery_prefix t := by
    intro Q Q' hU hV
    apply congrArg primalBlock
    apply scalar_runner_query_prefix A fill (joinedHaarFrame (Nat.le_of_lt hnd)) _
      (scalarHaarStage_prefix (Nat.le_of_lt hnd) profile tau lam c q p) seed t Q Q'
    intro i hi
    exact congrArg₂ joinBlocks (hU i hi) (hV i hi)
  dualQuery_prefix t := by
    intro Q Q' hU hV
    apply congrArg dualBlock
    apply scalar_runner_query_prefix A fill (joinedHaarFrame (Nat.le_of_lt hnd)) _
      (scalarHaarStage_prefix (Nat.le_of_lt hnd) profile tau lam c q p) seed t Q Q'
    intro i hi
    exact congrArg₂ joinBlocks (hU i hi) (hV i hi)
  primalOutput_prefix := by
    intro Q Q' hU hV
    apply congrArg primalBlock
    apply scalar_runner_output_prefix A fill (joinedHaarFrame (Nat.le_of_lt hnd)) _
      (scalarHaarStage_prefix (Nat.le_of_lt hnd) profile tau lam c q p) seed Q Q'
    intro i hi
    exact congrArg₂ joinBlocks (hU i hi) (hV i hi)
  dualOutput_prefix := by
    intro Q Q' hU hV
    apply congrArg dualBlock
    apply scalar_runner_output_prefix A fill (joinedHaarFrame (Nat.le_of_lt hnd)) _
      (scalarHaarStage_prefix (Nat.le_of_lt hnd) profile tau lam c q p) seed Q Q'
    intro i hi
    exact congrArg₂ joinBlocks (hU i hi) (hV i hi)
  primalQuery_norm t Q := by
    have h := (scalar_runner_query_feasible A fill
      (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) t (Q, seed)).1
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  dualQuery_norm t Q := by
    have h := (scalar_runner_query_feasible A fill
      (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) t (Q, seed)).2
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  primalOutput_norm Q := by
    have h := (scalar_runner_output_feasible A fill
      (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) (Q, seed)).1
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  dualOutput_norm Q := by
    have h := (scalar_runner_output_feasible A fill
      (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) (Q, seed)).2
    simpa only [Metric.mem_closedBall, dist_zero_right] using h

/-- Joint seed/frame measurability of the actual simultaneous source
slabs, including the unqueried saved output event. -/
theorem sourceHaarSlabEvent_measurable
    (hnd : N + 1 < d) (A : BallPolicy p d N R Seed mu) (fill : BallFeasible d R)
    (profile : GateProfile) (htau : tau ≠ 0) (lam c q s : ℝ) :
    MeasurableSet {w : (Haar.FrameSample d × Haar.FrameSample d) × Seed |
      w.1 ∈ Haar.pairedSlabEvent (sourceHaarProbes hnd A fill profile htau lam c q w.2) s} := by
  have hbad (i : Haar.PairedSlabIndex N) :
      MeasurableSet {w : (Haar.FrameSample d × Haar.FrameSample d) × Seed |
        w.1 ∈ Haar.pairedBadEvent (sourceHaarProbes hnd A fill profile htau lam c q w.2) s i} := by
    rcases i with ⟨block, a | a⟩ <;> cases block
    · change MeasurableSet {w : (Haar.FrameSample d × Haar.FrameSample d) × Seed |
        s < |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) w.1.1 (Haar.querySlabColumn a))
          (primalBlock (scalarRunnerQuery A fill (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) a.1 w))|}
      exact measurableSet_lt measurable_const
        ((((measurable_pi_apply (Haar.querySlabColumn a)).comp
          (measurable_haarStiefelFrame (Nat.le_of_lt hnd))).comp
            (measurable_fst.comp measurable_fst)).inner (𝕜 := ℝ)
          (sourceHaarQuery_primal_jointlyMeasurable hnd A fill profile htau lam c q a.1)).abs
    · change MeasurableSet {w : (Haar.FrameSample d × Haar.FrameSample d) × Seed |
        s < |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) w.1.2 (Haar.querySlabColumn a))
          (dualBlock (scalarRunnerQuery A fill (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) a.1 w))|}
      exact measurableSet_lt measurable_const
        ((((measurable_pi_apply (Haar.querySlabColumn a)).comp
          (measurable_haarStiefelFrame (Nat.le_of_lt hnd))).comp
            (measurable_snd.comp measurable_fst)).inner (𝕜 := ℝ)
          (sourceHaarQuery_dual_jointlyMeasurable hnd A fill profile htau lam c q a.1)).abs
    · change MeasurableSet {w : (Haar.FrameSample d × Haar.FrameSample d) × Seed |
        s < |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) w.1.1 (Fin.last N))
          (primalBlock (scalarRunnerOutput A fill (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) w))|}
      exact measurableSet_lt measurable_const
        ((((measurable_pi_apply (Fin.last N)).comp
          (measurable_haarStiefelFrame (Nat.le_of_lt hnd))).comp
            (measurable_fst.comp measurable_fst)).inner (𝕜 := ℝ)
          (sourceHaarOutput_primal_jointlyMeasurable hnd A fill profile htau lam c q)).abs
    · change MeasurableSet {w : (Haar.FrameSample d × Haar.FrameSample d) × Seed |
        s < |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) w.1.2 (Fin.last N))
          (dualBlock (scalarRunnerOutput A fill (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) w))|}
      exact measurableSet_lt measurable_const
        ((((measurable_pi_apply (Fin.last N)).comp
          (measurable_haarStiefelFrame (Nat.le_of_lt hnd))).comp
            (measurable_snd.comp measurable_fst)).inner (𝕜 := ℝ)
          (sourceHaarOutput_dual_jointlyMeasurable hnd A fill profile htau lam c q)).abs
  convert (MeasurableSet.iUnion hbad).compl using 1
  ext w
  simp only [Haar.pairedSlabEvent, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion]

end
end MinimaxAudit.Randomized
