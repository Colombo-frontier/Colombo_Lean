import Bilevel.ParameterizedStatefulAcceleratedPrimitive
import Bilevel.StatefulConfidenceLocal
import Bilevel.StatefulJointBatch
import Bilevel.BatchMean
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Executed anchor refresh with one full upper-gradient batch

The lower solve and full upper estimate share the original `HistorySFO`
kernel and thread its history. One full upper observation supplies both
blocks, preserving their correlation and counting one original SFO call.
The stored output retains the raw y block as well as its clipped version.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedAnchorProcedure
open Stateful PrimitiveGeometry

abbrev Input (X Y : Type*) := X × Y
abbrev Raw (X Y : Type*) := Y × Joint X Y
abbrev Stored (X Y : Type*) := Y × X × Y × Y

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

def lower (μ Lg D rA : ℝ) (q : ℕ) [NeZero q] : Procedure (Input X Y) History Y :=
  (StatefulConfidence.amplify
    (ParameterizedStatefulAccelerated.tiltedSolve O μ Lg 0 D (rA/12)) q).reparam
    (fun p : Input X Y => ((p.1,(0:Y)),p.2)) (by fun_prop)

def upper (η : ℝ) (q : ℕ) [NeZero q] : Procedure (X × Y) History (Joint X Y) :=
  StatefulConfidence.amplify (O.fullUpper.batchAtRadius (η/12)) q

def upperAfter (η : ℝ) (q : ℕ) [NeZero q] :
    Procedure ((Input X Y) × Y) History (Raw X Y) :=
  ((upper O η q).reparam (fun z => (z.1.1,z.2)) (by fun_prop)).map
    (fun z => (z.1.2,z.2)) (by fun_prop)

def refreshRaw (μ Lg D rA η : ℝ) (q : ℕ) [NeZero q] : Procedure (Input X Y) History (Raw X Y) :=
  (lower O μ Lg D rA q).bind (upperAfter O η q)

def store (Cf : ℝ) (z : Raw X Y) : Stored X Y :=
  (z.1,z.2.fst,z.2.snd,Clipping.clip Cf z.2.snd)

omit [CompleteSpace X] [SecondCountableTopology X] [CompleteSpace Y]
  [SecondCountableTopology (Joint X Y)] in
theorem store_measurable (Cf : ℝ) : Measurable (store (X := X) (Y := Y) Cf) := by
  have hpair := (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).continuous.measurable
  have hx : Measurable (fun z : Raw X Y => z.2.fst) := hpair.fst.comp measurable_snd
  have hy : Measurable (fun z : Raw X Y => z.2.snd) := hpair.snd.comp measurable_snd
  exact measurable_fst.prodMk (hx.prodMk
    (hy.prodMk (BatchMean.clip_stronglyMeasurable Cf hy.stronglyMeasurable).measurable))

def refresh (μ Lg Cf D rA η : ℝ) (q : ℕ) [NeZero q] : Procedure (Input X Y) History (Stored X Y) :=
  (refreshRaw O μ Lg D rA η q).map (fun z => store Cf z.2) ((store_measurable Cf).comp measurable_snd)

def reconstruct (z : Stored X Y) : Raw X Y := (z.1,pack z.2.1 z.2.2.1)

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem reconstruct_store (Cf : ℝ) (z : Raw X Y) : reconstruct (store Cf z) = z := rfl

omit [CompleteSpace X] [CompleteSpace Y] [SecondCountableTopology X] [SecondCountableTopology (Joint X Y)] in
theorem reconstruct_measurable : Measurable (reconstruct (X := X) (Y := Y)) := by
  exact measurable_fst.prodMk (packLinear.continuous.measurable.comp
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))))

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem store_clipped_bound (Cf : ℝ) (hCf : 0 ≤ Cf) (z : Raw X Y) :
    ‖(store Cf z).2.2.2‖ ≤ Cf := Clipping.bounded Cf hCf z.2.snd

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem lower_calls (μ Lg D rA : ℝ) (q : ℕ) [NeZero q] :
    (lower O μ Lg D rA q).CallsEq (fun _ =>
      q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (rA/12)) :=
  Procedure.CallsEq.reparam _ _ (StatefulConfidence.amplify_calls _ _
    (ParameterizedStatefulAccelerated.tiltedSolve_calls O μ Lg 0 D (rA/12)) q) _ _

theorem upper_calls (η : ℝ) (q : ℕ) [NeZero q] :
    (upper O η q).CallsEq (fun _ => q * FreshBatchKernel.count σf (η/12)) :=
  StatefulConfidence.amplify_calls _ _ (O.fullUpper.batchAtRadius_calls (η/12)) q

theorem upperAfter_calls (η : ℝ) (q : ℕ) [NeZero q] :
    (upperAfter O η q).CallsEq (fun _ => q * FreshBatchKernel.count σf (η/12)) :=
  Procedure.CallsEq.map _ _ (Procedure.CallsEq.reparam _ _ (upper_calls O η q) _ _) _ _

theorem refreshRaw_calls (μ Lg D rA η : ℝ) (q : ℕ) [NeZero q] :
    (refreshRaw O μ Lg D rA η q).CallsEq (fun _ =>
      q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (rA/12) +
        q * FreshBatchKernel.count σf (η/12)) :=
  Procedure.CallsEq.bind _ _ _ _ (lower_calls O μ Lg D rA q) (upperAfter_calls O η q)

theorem refresh_calls (μ Lg Cf D rA η : ℝ) (q : ℕ) [NeZero q] :
    (refresh O μ Lg Cf D rA η q).CallsEq (fun _ =>
      q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (rA/12) +
        q * FreshBatchKernel.count σf (η/12)) :=
  Procedure.CallsEq.map _ _ (refreshRaw_calls O μ Lg D rA η q) _ _

theorem upper_confidence (η : ℝ) (hη : 0 < η) (q : ℕ) [NeZero q] (x : X) (y : Y) (h : History) :
    ((upper O η q).law ((x,y),h)).real
      {z | η < ‖z.1 - pack (O.upper.truth_x (x,y)) (O.upper.truth_y (x,y))‖} ≤
      Real.exp (-(q:ℝ)/8) :=
  StatefulConfidence.amplify_confidence _ O.fullUpper.truth (fun _ => η) (fun _ => hη)
    (O.fullUpper.batchAtRadius_mse (η/12) (by linarith)) q (x,y) h

def badEvent (x : X) (ys : Y) (rA η : ℝ) : Set (Raw X Y) :=
  {z | rA < ‖z.1-ys‖ ∨ η < ‖z.2-O.fullUpper.truth (x,z.1)‖}

theorem badEvent_measurable (x : X) (ys : Y) (rA η : ℝ) :
    MeasurableSet (badEvent O x ys rA η) := by
  apply (measurableSet_lt measurable_const (measurable_fst.sub_const ys).norm).union
  exact measurableSet_lt measurable_const
    (measurable_snd.sub (O.fullUpper.truth_measurable.comp (measurable_const.prodMk measurable_fst))).norm

theorem upperAfter_failure_mean (η : ℝ) (hη : 0 < η) (q : ℕ) [NeZero q]
    (p : Input X Y) (ya ys : Y) (rA : ℝ) (h : History) :
    (∫ z, Bilevel.ConditionalConfidence.flag (badEvent O p.1 ys rA η) z.1
      ∂(upperAfter O η q).law ((p,ya),h)) ≤
        Bilevel.ConditionalConfidence.flag {y | rA < ‖y-ys‖} ya + Real.exp (-(q:ℝ)/8) := by
  let B := badEvent O p.1 ys rA η
  let G : Set (Joint X Y) := {v | η < ‖v-O.fullUpper.truth (p.1,ya)‖}
  have hB := badEvent_measurable O p.1 ys rA η
  have hG : MeasurableSet G := measurableSet_lt measurable_const (measurable_id.sub_const _).norm
  have hf : StronglyMeasurable (Bilevel.ConditionalConfidence.flag B) :=
    (measurable_const.indicator hB).stronglyMeasurable
  rw [upperAfter,Procedure.map_output_integral _ _ _ _ _ _ hf]
  change (∫ z, Bilevel.ConditionalConfidence.flag B (ya,z.1) ∂(upper O η q).law ((p.1,ya),h)) ≤ _
  have hi : Integrable (fun z : Outcome (Joint X Y) History => Bilevel.ConditionalConfidence.flag B (ya,z.1))
      ((upper O η q).law ((p.1,ya),h)) :=
    (integrable_const 1).indicator (hB.preimage (measurable_const.prodMk measurable_fst))
  have hj : Integrable (fun z : Outcome (Joint X Y) History => Bilevel.ConditionalConfidence.flag G z.1)
      ((upper O η q).law ((p.1,ya),h)) := (integrable_const 1).indicator (hG.preimage measurable_fst)
  have hpoint (z : Outcome (Joint X Y) History) :
      Bilevel.ConditionalConfidence.flag B (ya,z.1) ≤
        Bilevel.ConditionalConfidence.flag {y | rA < ‖y-ys‖} ya +
          Bilevel.ConditionalConfidence.flag G z.1 := by
    classical
    by_cases h₁ : rA < ‖ya-ys‖ <;> by_cases h₂ : η < ‖z.1-O.fullUpper.truth (p.1,ya)‖ <;>
      simp [B,G,badEvent,Bilevel.ConditionalConfidence.flag,Set.indicator_apply,h₁,h₂]
  have hb := integral_mono hi ((integrable_const _).add hj) hpoint
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_const _) hj, integral_const, measureReal_univ_eq_one, one_smul] at hb
  have he : (∫ z, Bilevel.ConditionalConfidence.flag G z.1 ∂(upper O η q).law ((p.1,ya),h)) =
      ((upper O η q).law ((p.1,ya),h)).real {z | z.1 ∈ G} := by
    simpa only [Bilevel.ConditionalConfidence.flag, smul_eq_mul, mul_one] using
      integral_indicator_const (μ := (upper O η q).law ((p.1,ya),h)) (1:ℝ) (hG.preimage measurable_fst)
  rw [he] at hb
  exact hb.trans (add_le_add_left (upper_confidence O η hη q p.1 ya h) _)

set_option maxHeartbeats 800000 in
theorem refreshRaw_union_bound (μ Lg D rA η : ℝ) (hη : 0 < η) (q : ℕ) [NeZero q]
    (p : Input X Y) (ys : Y)
    (hlower : ∀ h, ((lower O μ Lg D rA q).law (p,h)).real {z | rA < ‖z.1-ys‖} ≤
      Real.exp (-(q:ℝ)/8)) (h : History) :
    ((refreshRaw O μ Lg D rA η q).law (p,h)).real
      {z | z.1 ∈ badEvent O p.1 ys rA η} ≤ 2 * Real.exp (-(q:ℝ)/8) := by
  let B := badEvent O p.1 ys rA η
  let F : Set Y := {y | rA < ‖y-ys‖}
  have hB := badEvent_measurable O p.1 ys rA η
  have hF : MeasurableSet F := measurableSet_lt measurable_const (measurable_id.sub_const ys).norm
  have hi : Integrable (fun z : Outcome Y History => Bilevel.ConditionalConfidence.flag F z.1)
      ((lower O μ Lg D rA q).law (p,h)) := (integrable_const 1).indicator (hF.preimage measurable_fst)
  have hstep (z : Outcome Y History) :
      Integrable (fun w : Outcome (Raw X Y) History => Bilevel.ConditionalConfidence.flag B w.1)
        ((upperAfter O η q).law ((p,z.1),z.2.1)) :=
    (integrable_const 1).indicator (hB.preimage measurable_fst)
  have hb := Procedure.bind_output_bound (lower O μ Lg D rA q) (upperAfter O η q) p h
    (Bilevel.ConditionalConfidence.flag B) (measurable_const.indicator hB)
    (fun z => (Bilevel.ConditionalConfidence.flag_bounds B z).1)
    (fun y => Bilevel.ConditionalConfidence.flag F y + Real.exp (-(q:ℝ)/8))
    (hi.add (integrable_const _)) hstep
    (fun z => upperAfter_failure_mean O η hη q p z.1 ys rA z.2.1)
  have heB : (∫ z, Bilevel.ConditionalConfidence.flag B z.1
      ∂(refreshRaw O μ Lg D rA η q).law (p,h)) =
      ((refreshRaw O μ Lg D rA η q).law (p,h)).real {z | z.1 ∈ B} := by
    simpa only [Bilevel.ConditionalConfidence.flag, smul_eq_mul, mul_one] using
      integral_indicator_const (μ := (refreshRaw O μ Lg D rA η q).law (p,h)) (1:ℝ)
        (hB.preimage measurable_fst)
  have heF : (∫ z, Bilevel.ConditionalConfidence.flag F z.1 ∂(lower O μ Lg D rA q).law (p,h)) =
      ((lower O μ Lg D rA q).law (p,h)).real {z | z.1 ∈ F} := by
    simpa only [Bilevel.ConditionalConfidence.flag, smul_eq_mul, mul_one] using
      integral_indicator_const (μ := (lower O μ Lg D rA q).law (p,h)) (1:ℝ)
        (hF.preimage measurable_fst)
  have hb' := hb.2
  change (∫ z, Bilevel.ConditionalConfidence.flag B z.1
    ∂(refreshRaw O μ Lg D rA η q).law (p,h)) ≤ _ at hb'
  rw [heB,integral_add hi (integrable_const _),integral_const,measureReal_univ_eq_one,one_smul,heF] at hb'
  have hl := hlower h
  change ((lower O μ Lg D rA q).law (p,h)).real {z | z.1 ∈ F} ≤ _ at hl
  linarith

variable {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ) [FiniteDimensional ℝ Y] [Nontrivial Y]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  [Nontrivial Y] in
theorem untilted_response (x : X) : P.tiltedResponse x 0 (0:Y) = P.canonicalResponse.y x := by
  apply P.tilted_stationary_unique x 0 0
  · exact P.tiltedResponse_stationary x 0 0
  · simpa using P.canonicalResponse_stationary x

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem lower_confidence (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (D rA : ℝ) (hr : 0 < rA) (q : ℕ) [NeZero q] (p : Input X Y)
    (hinit : ‖p.2 - P.canonicalResponse.y p.1‖ ≤ D) (h : History) :
    ((lower O μ Lg D rA q).law (p,h)).real
      {z | rA < ‖z.1 - P.canonicalResponse.y p.1‖} ≤ Real.exp (-(q:ℝ)/8) := by
  have htilt := untilted_response P p.1
  have hcert : ∀ h, Integrable (fun z => ‖z.1-P.canonicalResponse.y p.1‖^2)
      ((ParameterizedStatefulAccelerated.tiltedSolve O μ Lg 0 D (rA/12)).law (((p.1,0),p.2),h)) ∧
      (∫ z, ‖z.1-P.canonicalResponse.y p.1‖^2
        ∂(ParameterizedStatefulAccelerated.tiltedSolve O μ Lg 0 D (rA/12)).law (((p.1,0),p.2),h)) ≤
          (rA/12)^2 := by
    intro h
    simpa only [htilt] using ParameterizedStatefulAccelerated.tiltedSolve_accuracy O P hgy p.1 0 0 p.2
      D (rA/12) (by linarith) (by simpa only [htilt] using hinit) h
  exact StatefulConfidence.amplify_confidence_at _ ((p.1,0),p.2)
    (P.canonicalResponse.y p.1) rA hr hcert q h

/-- Joint anchor certificate for the actual history-threaded refresh.
Both failures together have probability at most twice the confidence tail. -/
theorem refreshRaw_confidence (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (D rA η : ℝ) (hr : 0 < rA) (hη : 0 < η) (q : ℕ) [NeZero q] (p : Input X Y)
    (hinit : ‖p.2-P.canonicalResponse.y p.1‖ ≤ D) (h : History) :
    ((refreshRaw O μ Lg D rA η q).law (p,h)).real
      {z | z.1 ∈ badEvent O p.1 (P.canonicalResponse.y p.1) rA η} ≤
        2 * Real.exp (-(q:ℝ)/8) :=
  refreshRaw_union_bound O μ Lg D rA η hη q p (P.canonicalResponse.y p.1)
    (fun h => lower_confidence O P hgy D rA hr q p hinit h) h

/-- The same joint certificate on the stored output, which contains both
the raw full-gradient pair and the clipped frozen direction. -/
theorem refresh_confidence (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (D rA η : ℝ) (hr : 0 < rA) (hη : 0 < η) (q : ℕ) [NeZero q] (p : Input X Y)
    (hinit : ‖p.2-P.canonicalResponse.y p.1‖ ≤ D) (h : History) :
    ((refresh O μ Lg Cf D rA η q).law (p,h)).real
      {z | reconstruct z.1 ∈ badEvent O p.1 (P.canonicalResponse.y p.1) rA η} ≤
        2 * Real.exp (-(q:ℝ)/8) := by
  have hm : Measurable (fun z : Outcome (Raw X Y) History => (store Cf z.1,z.2)) :=
    ((store_measurable Cf).comp measurable_fst).prodMk measurable_snd
  have hs : MeasurableSet {z : Outcome (Stored X Y) History |
      reconstruct z.1 ∈ badEvent O p.1 (P.canonicalResponse.y p.1) rA η} :=
    (badEvent_measurable O p.1 (P.canonicalResponse.y p.1) rA η).preimage
      (reconstruct_measurable.comp measurable_fst)
  rw [refresh,Procedure.map_law,measureReal_def,Measure.map_apply hm hs]
  change ((refreshRaw O μ Lg D rA η q).law (p,h)).real
    {z | reconstruct (store Cf z.1) ∈ badEvent O p.1 (P.canonicalResponse.y p.1) rA η} ≤ _
  simp only [reconstruct_store]
  exact refreshRaw_confidence O P hgy D rA η hr hη q p hinit h

end Bilevel.CachedAnchorProcedure
