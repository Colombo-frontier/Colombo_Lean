import Bilevel.CachedEstimatorConfidence
import Bilevel.StatefulFailureBounds

/-! Four-operation union bound for the executed cached estimator. Targets of
both gradient means depend on the actually sampled lower points. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.CachedEstimatorProcedure
open Stateful ConditionalConfidence

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

def solveBad (ys yt : Y) (r : ℝ) : Set (Y × Y) :=
  {z | r < ‖z.1 - ys‖ ∨ r < ‖z.2 - yt‖}

def firstBad (x : X) (ys yt : Y) (r δ : ℝ) : Set ((Y × Y) × X) :=
  {z | z.1 ∈ solveBad ys yt r ∨ δ < ‖z.2 - O.lower.truth_x (x,z.1.1)‖}

def badEvent (x : X) (ys yt : Y) (r δ : ℝ) : Set (Transcript X Y) :=
  {z | (z.1,z.2.1) ∈ firstBad O x ys yt r δ ∨
    δ < ‖z.2.2 - O.lower.truth_x (x,z.1.2)‖}

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [InnerProductSpace ℝ Y] [CompleteSpace Y] [SecondCountableTopology Y] in
theorem solveBad_measurable (ys yt : Y) (r : ℝ) : MeasurableSet (solveBad ys yt r) :=
  (measurableSet_lt measurable_const (measurable_fst.sub_const ys).norm).union
    (measurableSet_lt measurable_const (measurable_snd.sub_const yt).norm)

theorem firstBad_measurable (x : X) (ys yt : Y) (r δ : ℝ) :
    MeasurableSet (firstBad O x ys yt r δ) :=
  ((solveBad_measurable ys yt r).preimage measurable_fst).union
    (measurableSet_lt measurable_const
      (measurable_snd.sub (O.gx.truth_measurable.comp
        (measurable_const.prodMk (measurable_fst.comp measurable_fst)))).norm)

theorem badEvent_measurable (x : X) (ys yt : Y) (r δ : ℝ) :
    MeasurableSet (badEvent O x ys yt r δ) :=
  ((firstBad_measurable O x ys yt r δ).preimage
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).union
    (measurableSet_lt measurable_const
      ((measurable_snd.comp measurable_snd).sub (O.gx.truth_measurable.comp
        (measurable_const.prodMk (measurable_snd.comp measurable_fst)))).norm)

theorem gxMean_truth_confidence (δ : ℝ) (hδ : 0 < δ) (q : ℕ) [NeZero q]
    (x : X) (y : Y) (h : History) :
    ((gxMean O δ q).law ((x,y),h)).real
      {z | δ < ‖z.1 - O.lower.truth_x (x,y)‖} ≤ Real.exp (-(q : ℝ) / 8) :=
  StatefulConfidence.amplify_confidence_at _ (x,y) (O.lower.truth_x (x,y)) δ hδ
    (fun h' => O.gx.batchAtRadius_mse (δ / 12) (by positivity) (x,y) h') q h

theorem solvePair_union_bound (μ Lg t D r : ℝ) (q : ℕ) [NeZero q]
    (p : Input X Y) (ys yt : Y)
    (h₀ : ∀ h, ((untilted O μ Lg D r q).law (p,h)).real
      {z | r < ‖z.1 - ys‖} ≤ Real.exp (-(q : ℝ) / 8))
    (hₜ : ∀ h, ((tilted O μ Lg t D r q).law (p,h)).real
      {z | r < ‖z.1 - yt‖} ≤ Real.exp (-(q : ℝ) / 8)) (h : History) :
    ((solvePair O μ Lg t D r q).law (p,h)).real
      {z | z.1 ∈ solveBad ys yt r} ≤ 2 * Real.exp (-(q : ℝ) / 8) := by
  classical
  have hF : MeasurableSet {y : Y | r < ‖y-ys‖} :=
    measurableSet_lt measurable_const (measurable_id.sub_const ys).norm
  have hG : MeasurableSet {y : Y | r < ‖y-yt‖} :=
    measurableSet_lt measurable_const (measurable_id.sub_const yt).norm
  have hh := Procedure.bind_failure_bound (untilted O μ Lg D r q)
    (((tilted O μ Lg t D r q).reparam Prod.fst measurable_fst).map
      (fun z => (z.1.2, z.2)) (by fun_prop)) p h _ hF _
      (solveBad_measurable ys yt r) (h₀ h) (fun y h' => by
        have hm := Procedure.map_failure_union_bound
          ((tilted O μ Lg t D r q).reparam Prod.fst measurable_fst)
          (fun z => (z.1.2,z.2)) (by fun_prop) (p,y) h'
          (solveBad ys yt r) (solveBad_measurable ys yt r) _ hG
          (r < ‖y-ys‖) (fun _ hz => hz) (hₜ h')
        simpa only [flag, Set.indicator_apply, Set.mem_setOf_eq] using hm)
  simpa only [two_mul] using hh

theorem firstGradient_failure (δ : ℝ) (hδ : 0 < δ) (q : ℕ) [NeZero q]
    (p : Input X Y) (v : Y × Y) (ys yt : Y) (r : ℝ) (h : History) :
    ((firstGradient O δ q).law ((p,v),h)).real
      {z | z.1 ∈ firstBad O p.1 ys yt r δ} ≤
        flag (solveBad ys yt r) v + Real.exp (-(q : ℝ) / 8) := by
  classical
  have hm := Procedure.map_failure_union_bound
    ((gxMean O δ q).reparam (fun z : (Input X Y) × (Y × Y) => (z.1.1,z.2.1)) (by fun_prop))
    (fun z => (z.1.2,z.2)) (by fun_prop) (p,v) h
    (firstBad O p.1 ys yt r δ) (firstBad_measurable O p.1 ys yt r δ)
    {a | δ < ‖a - O.lower.truth_x (p.1,v.1)‖}
    (measurableSet_lt measurable_const (measurable_id.sub_const _).norm)
    (v ∈ solveBad ys yt r) (fun _ hz => hz) (gxMean_truth_confidence O δ hδ q p.1 v.1 h)
  simpa only [flag, Set.indicator_apply] using hm

theorem lastGradient_failure (δ : ℝ) (hδ : 0 < δ) (q : ℕ) [NeZero q]
    (p : Input X Y) (v : (Y × Y) × X) (ys yt : Y) (r : ℝ) (h : History) :
    ((lastGradient O δ q).law ((p,v),h)).real
      {z | z.1 ∈ badEvent O p.1 ys yt r δ} ≤
        flag (firstBad O p.1 ys yt r δ) v + Real.exp (-(q : ℝ) / 8) := by
  classical
  have hm := Procedure.map_failure_union_bound
    ((gxMean O δ q).reparam (fun z : (Input X Y) × ((Y × Y) × X) => (z.1.1,z.2.1.2)) (by fun_prop))
    (fun z => (z.1.2.1,(z.1.2.2,z.2))) (by fun_prop) (p,v) h
    (badEvent O p.1 ys yt r δ) (badEvent_measurable O p.1 ys yt r δ)
    {a | δ < ‖a - O.lower.truth_x (p.1,v.1.2)‖}
    (measurableSet_lt measurable_const (measurable_id.sub_const _).norm)
    (v ∈ firstBad O p.1 ys yt r δ) (fun _ hz => hz)
    (gxMean_truth_confidence O δ hδ q p.1 v.1.2 h)
  simpa only [flag, Set.indicator_apply] using hm

theorem transcript_union_bound (μ Lg t D r δ : ℝ) (hδ : 0 < δ) (q : ℕ) [NeZero q]
    (p : Input X Y) (ys yt : Y)
    (h₀ : ∀ h, ((untilted O μ Lg D r q).law (p,h)).real
      {z | r < ‖z.1 - ys‖} ≤ Real.exp (-(q : ℝ) / 8))
    (hₜ : ∀ h, ((tilted O μ Lg t D r q).law (p,h)).real
      {z | r < ‖z.1 - yt‖} ≤ Real.exp (-(q : ℝ) / 8)) (h : History) :
    ((transcript O μ Lg t D r δ q).law (p,h)).real
      {z | z.1 ∈ badEvent O p.1 ys yt r δ} ≤ 4 * Real.exp (-(q : ℝ) / 8) := by
  have h1 := Procedure.bind_failure_bound (solvePair O μ Lg t D r q) (firstGradient O δ q)
    p h _ (solveBad_measurable ys yt r) _ (firstBad_measurable O p.1 ys yt r δ)
    (solvePair_union_bound O μ Lg t D r q p ys yt h₀ hₜ h)
    (fun v h' => firstGradient_failure O δ hδ q p v ys yt r h')
  have h2 := Procedure.bind_failure_bound
    ((solvePair O μ Lg t D r q).bind (firstGradient O δ q)) (lastGradient O δ q)
    p h _ (firstBad_measurable O p.1 ys yt r δ) _ (badEvent_measurable O p.1 ys yt r δ)
    h1 (fun v h' => lastGradient_failure O δ hδ q p v ys yt r h')
  exact h2.trans (by ring_nf; rfl)

variable {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)
  [FiniteDimensional ℝ Y] [Nontrivial Y]

theorem transcript_confidence (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (t D r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (q : ℕ) [NeZero q]
    (p : Input X Y)
    (h₀ : ‖p.2.2.2 - P.canonicalResponse.y p.1‖ ≤ D)
    (hₜ : ‖p.2.2.2 - P.tiltedResponse p.1 t p.2.2.1‖ ≤ D) (h : History) :
    ((transcript O μ Lg t D r δ q).law (p,h)).real
      {z | z.1 ∈ badEvent O p.1 (P.canonicalResponse.y p.1)
        (P.tiltedResponse p.1 t p.2.2.1) r δ} ≤ 4 * Real.exp (-(q : ℝ) / 8) :=
  transcript_union_bound O μ Lg t D r δ hδ q p _ _
    (fun h' => untilted_confidence O P hgy D r hr q p h₀ h')
    (fun h' => tilted_confidence O P hgy t D r hr q p hₜ h') h

end Bilevel.CachedEstimatorProcedure
