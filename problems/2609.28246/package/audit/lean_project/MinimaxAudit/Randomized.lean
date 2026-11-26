import MinimaxAudit.RandomizedSimulation
import MinimaxAudit.FullJetParameter

/-!
# Actual randomized scalar-jet transcript theorem

The final frame pair is fixed independently of the realized seed. The policy
is the source total-history Borel policy, and its output is evaluated by the
same `runScalarPolicy` as in the deterministic theorem. All full-jet hiding,
measurable execution, adapted Haar concentration, finite union probability,
and fixed-frame averaging steps are proved in the imported modules.
-/
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace MinimaxAudit.Randomized
open Deterministic MeasurableExecution VIReference.Pilot
noncomputable section
set_option maxHeartbeats 1000000

variable {N d p : ℕ} {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed} {R : ℝ}

theorem source_virtual_output_eq_actual_on_slabs
    (hnd : N + 1 < d)
    (A : RandomizedScalarPolicy p d d N (Metric.closedBall 0 R) (Metric.closedBall 0 R) Seed mu)
    (fill : productDomain (Metric.closedBall (0 : Primal d) R) (Metric.closedBall (0 : Dual d) R))
    (profile : GateProfile) {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ)
    (Q : Haar.FrameSample d × Haar.FrameSample d) (seed : Seed)
    (hgood : Q ∈ Haar.pairedSlabEvent
      (sourceHaarProbes hnd A fill profile htau.ne' lam c q seed) (tau / (8 * Real.sqrt 2))) :
    scalarRunnerOutput A fill (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) (Q, seed) =
      runScalarPolicy (A.policy seed)
        (scalarHaarActual (Nat.le_of_lt hnd) profile tau lam c q p Q) N [] := by
  apply scalar_runner_coupled_eq_source_run A fill
    (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p)
    (scalarHaarActual (Nat.le_of_lt hnd) profile tau lam c q p) (Q, seed)
  intro t
  apply scalarHaarStage_eq_actual_of_slabs (Nat.le_of_lt hnd) profile htau lam c q p t Q
  intro i hti
  have hs := Haar.query_slabs_of_pairedSlabEvent
    (sourceHaarProbes hnd A fill profile htau.ne' lam c q seed) hgood t i hti
  exact hs

/-- The actual policy output has small a_n and b_n on the proved Haar event;
no output-oracle call or update-rule restriction is imposed. -/
theorem source_actual_output_coordinates_on_slabs
    (hnd : N + 1 < d)
    (A : RandomizedScalarPolicy p d d N (Metric.closedBall 0 R) (Metric.closedBall 0 R) Seed mu)
    (fill : productDomain (Metric.closedBall (0 : Primal d) R) (Metric.closedBall (0 : Dual d) R))
    (profile : GateProfile) {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ)
    (Q : Haar.FrameSample d × Haar.FrameSample d) (seed : Seed)
    (hgood : Q ∈ Haar.pairedSlabEvent
      (sourceHaarProbes hnd A fill profile htau.ne' lam c q seed) (tau / (8 * Real.sqrt 2))) :
    let U := (haarParameters (Nat.le_of_lt hnd) Q).1
    let V := (haarParameters (Nat.le_of_lt hnd) Q).2
    let output := runScalarPolicy (A.policy seed)
      (scalarHaarActual (Nat.le_of_lt hnd) profile tau lam c q p Q) N []
    |plusForm U V (Fin.last N) output| ≤ tau / 8 ∧
      |minusForm U V (Fin.last N) output| ≤ tau / 8 := by
  have hs := Haar.output_slabs_of_pairedSlabEvent
    (sourceHaarProbes hnd A fill profile htau.ne' lam c q seed) hgood
  have hcoords := paired_forms_slabs htau
    (haarParameters (Nat.le_of_lt hnd) Q).1 (haarParameters (Nat.le_of_lt hnd) Q).2
    (Fin.last N)
    (scalarRunnerOutput A fill (scalarHaarStage (Nat.le_of_lt hnd) profile tau lam c q p) (Q, seed))
    hs.1 hs.2
  rw [source_virtual_output_eq_actual_on_slabs hnd A fill profile htau lam c q Q seed hgood] at hcoords
  exact hcoords

/-- The actual randomized information theorem: one fixed scalar hard
potential hides the final paired coordinates for at least 3/4 of the policy's
independent seeds. All query/jet/transcript assumptions have been discharged
from the source policy and the concrete scalar construction. -/
theorem exists_randomized_fixed_pair_output_slabs
    (hnd : N + 1 < d) (hR : 0 < R)
    (A : RandomizedScalarPolicy p d d N (Metric.closedBall 0 R) (Metric.closedBall 0 R) Seed mu)
    (fill : productDomain (Metric.closedBall (0 : Primal d) R) (Metric.closedBall (0 : Dual d) R))
    (profile : GateProfile) {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ)
    (hdim : 2 * R ^ 2 / (tau / (8 * Real.sqrt 2)) ^ 2 *
      Real.log (8 * (((N + 1) * (N + 2) : ℕ) : ℝ)) ≤
      ((d - (N + 1) : ℕ) : ℝ)) :
    ∃ (U : Fin (N + 1) → Primal d) (V : Fin (N + 1) → Dual d),
      Orthonormal ℝ U ∧ Orthonormal ℝ V ∧
      (3 / 4 : ℝ≥0∞) ≤ mu {seed |
        let output := runScalarPolicy (A.policy seed)
          (exactScalarJet p (hardPotential profile tau lam c q U V)) N []
        |plusForm U V (Fin.last N) output| ≤ tau / 8 ∧
          |minusForm U V (Fin.last N) output| ≤ tau / 8} := by
  letI : IsProbabilityMeasure mu := A.probability
  have hs : 0 < tau / (8 * Real.sqrt 2) := by positivity
  obtain ⟨Q, hQ⟩ := Haar.exists_fixed_pair_seed_slabs mu hR hs
    (sourceHaarProbes hnd A fill profile htau.ne' lam c q)
    (sourceHaarSlabEvent_measurable hnd A fill profile htau.ne' lam c q _) hdim
  refine ⟨(haarParameters (Nat.le_of_lt hnd) Q).1,
    (haarParameters (Nat.le_of_lt hnd) Q).2,
    orthonormal_haarStiefelFrame _ Q.1, orthonormal_haarStiefelFrame _ Q.2, ?_⟩
  apply hQ.trans
  apply measure_mono
  intro seed hseed
  exact source_actual_output_coordinates_on_slabs hnd A fill profile htau lam c q Q seed hseed

/-- Joint measurability of the actual full scalar oracle, with no truncation. -/
theorem scalarHaarActual_jointlyMeasurable
    (hnd : N + 1 ≤ d) (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0)
    (lam c q : ℝ) :
    Measurable (fun z : (Haar.FrameSample d × Haar.FrameSample d) × SaddleSpace d d =>
      scalarHaarActual hnd profile tau lam c q p z.1 z.2) := by
  let f : FrameParameters N d d × SaddleSpace d d → ScalarJet p (SaddleSpace d d) :=
    fun z => exactScalarJet p (hardPotential profile tau lam c q z.1.1 z.1.2) z.2
  let g : (Haar.FrameSample d × Haar.FrameSample d) × SaddleSpace d d →
      FrameParameters N d d × SaddleSpace d d := fun z => (haarParameters hnd z.1, z.2)
  have hf : Measurable f := fullScalarJet_jointlyMeasurable
    (N := N) (dx := d) (dy := d) profile htau lam c q p
  have hp : Measurable (fun z : (Haar.FrameSample d × Haar.FrameSample d) × SaddleSpace d d =>
      haarParameters hnd z.1) := (haarParameters_measurable hnd).comp
        (measurable_fst : Measurable (Prod.fst :
          (Haar.FrameSample d × Haar.FrameSample d) × SaddleSpace d d →
            Haar.FrameSample d × Haar.FrameSample d))
  have hg : Measurable g := hp.prodMk
    (measurable_snd : Measurable (Prod.snd :
      (Haar.FrameSample d × Haar.FrameSample d) × SaddleSpace d d → SaddleSpace d d))
  change Measurable (f ∘ g)
  exact hf.comp hg

/-- The actual output, rather than only the simulated output, is jointly
measurable in a frame fixed before the run and the independent algorithm seed. -/
theorem source_actual_output_jointlyMeasurable
    (hnd : N + 1 ≤ d)
    (A : RandomizedScalarPolicy p d d N (Metric.closedBall 0 R) (Metric.closedBall 0 R) Seed mu)
    (fill : productDomain (Metric.closedBall (0 : Primal d) R) (Metric.closedBall (0 : Dual d) R))
    (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0) (lam c q : ℝ) :
    Measurable (fun w : (Haar.FrameSample d × Haar.FrameSample d) × Seed =>
      runScalarPolicy (A.policy w.2)
        (scalarHaarActual hnd profile tau lam c q p w.1) N []) := by
  have hm := (scalar_runner_jointly_measurable A fill
    (fun Q _ => scalarHaarActual hnd profile tau lam c q p Q)
    (fun _ => scalarHaarActual_jointlyMeasurable (p := p) hnd profile htau lam c q)).2
  convert hm using 1
  funext w
  exact (scalar_runner_fixed_eq_source_run A fill
    (scalarHaarActual hnd profile tau lam c q p) w).symm

/-- The precise actual-output event used in the fixed-frame information
bound is Borel-measurable on the joint frame/seed space. -/
theorem source_actual_coordinate_event_measurable
    (hnd : N + 1 ≤ d)
    (A : RandomizedScalarPolicy p d d N (Metric.closedBall 0 R) (Metric.closedBall 0 R) Seed mu)
    (fill : productDomain (Metric.closedBall (0 : Primal d) R) (Metric.closedBall (0 : Dual d) R))
    (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0) (lam c q : ℝ) (bound : ℝ) :
    MeasurableSet {w : (Haar.FrameSample d × Haar.FrameSample d) × Seed |
      let output := runScalarPolicy (A.policy w.2)
        (scalarHaarActual hnd profile tau lam c q p w.1) N []
      |plusForm (haarParameters hnd w.1).1 (haarParameters hnd w.1).2 (Fin.last N) output| ≤ bound ∧
      |minusForm (haarParameters hnd w.1).1 (haarParameters hnd w.1).2 (Fin.last N) output| ≤ bound} := by
  have ho := source_actual_output_jointlyMeasurable hnd A fill profile htau lam c q
  have hp : Measurable (fun w : (Haar.FrameSample d × Haar.FrameSample d) × Seed =>
      haarParameters hnd w.1) := (haarParameters_measurable hnd).comp measurable_fst
  have ha := ((joint_plusForm_contDiff (N := N) (dx := d) (dy := d)
    (Fin.last N)).continuous.measurable).comp (hp.prodMk ho)
  have hb := ((joint_minusForm_contDiff (N := N) (dx := d) (dy := d)
    (Fin.last N)).continuous.measurable).comp (hp.prodMk ho)
  exact (measurableSet_le ha.abs measurable_const).inter
    (measurableSet_le hb.abs measurable_const)

end
end MinimaxAudit.Randomized
