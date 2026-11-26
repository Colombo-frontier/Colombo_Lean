import Bilevel.ParameterizedStatefulAcceleratedPrimitive
import Bilevel.StatefulConfidence
import Bilevel.CachedTiltError

/-! The current-point cached hypergradient computation as an actual original
SFO procedure. The stored upper blocks are input data and are reused directly.
The output transcript retains the two solved points and two sampled lower
gradient blocks so that all four accuracy events remain observable in proofs. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.CachedEstimatorProcedure
open Stateful

abbrev Input (X Y : Type*) := X × X × Y × Y
abbrev Transcript (X Y : Type*) := (Y × Y) × (X × X)

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

def untilted (μ Lg D r : ℝ) (q : ℕ) [NeZero q] : Procedure (Input X Y) History Y :=
  (StatefulConfidence.amplify
    (ParameterizedStatefulAccelerated.tiltedSolve O μ Lg 0 D (r / 12)) q).reparam
    (fun p : Input X Y => ((p.1, (0 : Y)), p.2.2.2)) (by fun_prop)

def tilted (μ Lg t D r : ℝ) (q : ℕ) [NeZero q] : Procedure (Input X Y) History Y :=
  (StatefulConfidence.amplify
    (ParameterizedStatefulAccelerated.tiltedSolve O μ Lg t D (r / 12)) q).reparam
    (fun p : Input X Y => ((p.1, p.2.2.1), p.2.2.2)) (by fun_prop)

def solvePair (μ Lg t D r : ℝ) (q : ℕ) [NeZero q] : Procedure (Input X Y) History (Y × Y) :=
  (untilted O μ Lg D r q).bind
    (((tilted O μ Lg t D r q).reparam Prod.fst measurable_fst).map
      (fun z => (z.1.2, z.2)) (by fun_prop))

def gxMean (δ : ℝ) (q : ℕ) [NeZero q] : Procedure (X × Y) History X :=
  StatefulConfidence.amplify (O.gx.batchAtRadius (δ / 12)) q

def firstGradient (δ : ℝ) (q : ℕ) [NeZero q] :
    Procedure ((Input X Y) × (Y × Y)) History ((Y × Y) × X) :=
  ((gxMean O δ q).reparam (fun z => (z.1.1, z.2.1)) (by fun_prop)).map
    (fun z => (z.1.2, z.2)) (by fun_prop)

def lastGradient (δ : ℝ) (q : ℕ) [NeZero q] :
    Procedure ((Input X Y) × ((Y × Y) × X)) History (Transcript X Y) :=
  ((gxMean O δ q).reparam (fun z => (z.1.1, z.2.1.2)) (by fun_prop)).map
    (fun z => (z.1.2.1, (z.1.2.2, z.2))) (by fun_prop)

def transcript (μ Lg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    Procedure (Input X Y) History (Transcript X Y) :=
  ((solvePair O μ Lg t D r q).bind (firstGradient O δ q)).bind (lastGradient O δ q)

def estimate (t : ℝ) (p : Input X Y) (z : Transcript X Y) : X :=
  p.2.1 + t⁻¹ • (z.2.2 - z.2.1)

def estimator (μ Lg t D r δ : ℝ) (q : ℕ) [NeZero q] : Procedure (Input X Y) History X :=
  (transcript O μ Lg t D r δ q).map (fun z => estimate t z.1 z.2) (by
    unfold estimate
    fun_prop)

theorem untilted_calls (μ Lg D r : ℝ) (q : ℕ) [NeZero q] :
    (untilted O μ Lg D r q).CallsEq (fun _ =>
      q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ / Lg)) σg D (r / 12)) :=
  Procedure.CallsEq.reparam _ _
    (StatefulConfidence.amplify_calls _ _
      (ParameterizedStatefulAccelerated.tiltedSolve_calls O μ Lg 0 D (r / 12)) q) _ _

theorem tilted_calls (μ Lg t D r : ℝ) (q : ℕ) [NeZero q] :
    (tilted O μ Lg t D r q).CallsEq (fun _ =>
      q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ / Lg)) σg D (r / 12)) :=
  Procedure.CallsEq.reparam _ _
    (StatefulConfidence.amplify_calls _ _
      (ParameterizedStatefulAccelerated.tiltedSolve_calls O μ Lg t D (r / 12)) q) _ _

theorem solvePair_calls (μ Lg t D r : ℝ) (q : ℕ) [NeZero q] :
    (solvePair O μ Lg t D r q).CallsEq (fun _ =>
      2 * (q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ / Lg)) σg D (r / 12))) := by
  have ht := Procedure.CallsEq.map _ _
    (Procedure.CallsEq.reparam _ _ (tilted_calls O μ Lg t D r q) Prod.fst measurable_fst)
    (fun z : ((Input X Y) × Y) × Y => (z.1.2, z.2)) (by fun_prop)
  have hc := Procedure.CallsEq.bind (untilted O μ Lg D r q) _
    (fun _ => q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ / Lg)) σg D (r / 12))
    (fun _ => q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ / Lg)) σg D (r / 12))
    (untilted_calls O μ Lg D r q) ht
  simpa only [two_mul] using hc

theorem gxMean_calls (δ : ℝ) (q : ℕ) [NeZero q] :
    (gxMean O δ q).CallsEq (fun _ => q * FreshBatchKernel.count σg (δ / 12)) :=
  StatefulConfidence.amplify_calls _ _ (O.gx.batchAtRadius_calls (δ / 12)) q

theorem firstGradient_calls (δ : ℝ) (q : ℕ) [NeZero q] :
    (firstGradient O δ q).CallsEq (fun _ => q * FreshBatchKernel.count σg (δ / 12)) :=
  Procedure.CallsEq.map _ _ (Procedure.CallsEq.reparam _ _ (gxMean_calls O δ q) _ _) _ _

theorem lastGradient_calls (δ : ℝ) (q : ℕ) [NeZero q] :
    (lastGradient O δ q).CallsEq (fun _ => q * FreshBatchKernel.count σg (δ / 12)) :=
  Procedure.CallsEq.map _ _ (Procedure.CallsEq.reparam _ _ (gxMean_calls O δ q) _ _) _ _

theorem transcript_calls (μ Lg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    (transcript O μ Lg t D r δ q).CallsEq (fun _ =>
      2 * (q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ / Lg)) σg D (r / 12)) +
        2 * (q * FreshBatchKernel.count σg (δ / 12))) := by
  have h1 := Procedure.CallsEq.bind (solvePair O μ Lg t D r q) (firstGradient O δ q) _
    (fun _ : Input X Y => q * FreshBatchKernel.count σg (δ / 12))
    (solvePair_calls O μ Lg t D r q)
    (firstGradient_calls O δ q)
  have h2 := Procedure.CallsEq.bind
    ((solvePair O μ Lg t D r q).bind (firstGradient O δ q)) (lastGradient O δ q) _
    (fun _ : Input X Y => q * FreshBatchKernel.count σg (δ / 12)) h1 (lastGradient_calls O δ q)
  simpa only [two_mul, add_assoc] using h2

theorem estimator_calls (μ Lg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    (estimator O μ Lg t D r δ q).CallsEq (fun _ =>
      2 * (q * StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ / Lg)) σg D (r / 12)) +
        2 * (q * FreshBatchKernel.count σg (δ / 12))) :=
  Procedure.CallsEq.map _ _ (transcript_calls O μ Lg t D r δ q) _ _

variable {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ) [FiniteDimensional ℝ Y]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
/-- Deterministic error of the actual estimator map applied to its retained
transcript; the stored upper-gradient errors remain visible. -/
theorem estimate_error (p : Input X Y) (z : Transcript X Y) {t : ℝ} (ht : 0 < t) :
    ‖estimate t p z - gradient (P.hyperobjective P.canonicalResponse) p.1‖ ≤
      ‖p.2.1 - P.fx p.1 (P.canonicalResponse.y p.1)‖ +
      Lg / μ * ‖p.2.2.1 - P.fy p.1 (P.canonicalResponse.y p.1)‖ +
      t⁻¹ * (Lg * ‖z.1.2 - P.tiltedResponse p.1 t p.2.2.1‖ +
        Lg * ‖z.1.1 - P.canonicalResponse.y p.1‖ +
        ‖z.2.2 - P.gx p.1 z.1.2‖ + ‖z.2.1 - P.gx p.1 z.1.1‖) +
      ((1 + Lg / μ) * ρ * Cf ^ 2 / (2 * μ ^ 2)) * t := by
  have hh := P.cached_gradient_error P.canonicalResponse p.1 z.1.1 z.1.2 p.2.2.1 p.2.1
    (z.2.1 - P.gx p.1 z.1.1) (z.2.2 - P.gx p.1 z.1.2) ht
  have hc (a b : X) : a + (b - a) = b := by abel
  simpa only [Model.Primitive.cachedEstimator, estimate, hc] using hh

end Bilevel.CachedEstimatorProcedure
