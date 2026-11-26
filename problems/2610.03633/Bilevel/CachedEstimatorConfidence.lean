import Bilevel.CachedEstimatorProcedure
import Bilevel.StatefulConfidenceLocal

/-! Conditional confidence for each actual cached-estimator operation.
Each bound holds for every entering full history, at a certified current
input. No initialization hypothesis is imposed at unrelated invalid inputs. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.CachedEstimatorProcedure
open Stateful

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace History] {σf σg μ Lf Lg Cf ρ : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)
  [FiniteDimensional ℝ Y] [Nontrivial Y]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] [Nontrivial Y] in
theorem zero_tilt_response (x : X) : P.tiltedResponse x 0 (0 : Y) = P.canonicalResponse.y x := by
  apply P.lower_solution_unique x _ _ _ (P.canonicalResponse.minimizes x)
  intro y
  simpa only [Model.Primitive.tiltedLower, zero_mul, add_zero] using
    P.tiltedResponse_minimizes x 0 (0 : Y) y

theorem untilted_confidence (hgy : ∀ x y, O.lower.truth_y (x, y) = P.gy x y)
    (D r : ℝ) (hr : 0 < r) (q : ℕ) [NeZero q] (p : Input X Y)
    (hinit : ‖p.2.2.2 - P.canonicalResponse.y p.1‖ ≤ D) (h : History) :
    ((untilted O μ Lg D r q).law (p, h)).real
      {z | r < ‖z.1 - P.canonicalResponse.y p.1‖} ≤ Real.exp (-(q : ℝ) / 8) := by
  have hzero := zero_tilt_response P p.1
  have hmse (h' : History) := ParameterizedStatefulAccelerated.tiltedSolve_accuracy O P hgy
    p.1 0 (0 : Y) p.2.2.2 D (r / 12) (by positivity)
    (by simpa only [hzero] using hinit) h'
  simp only [hzero] at hmse
  exact StatefulConfidence.amplify_confidence_at
    (ParameterizedStatefulAccelerated.tiltedSolve O μ Lg 0 D (r / 12))
    ((p.1, (0 : Y)), p.2.2.2) (P.canonicalResponse.y p.1) r hr hmse q h

theorem tilted_confidence (hgy : ∀ x y, O.lower.truth_y (x, y) = P.gy x y)
    (t D r : ℝ) (hr : 0 < r) (q : ℕ) [NeZero q] (p : Input X Y)
    (hinit : ‖p.2.2.2 - P.tiltedResponse p.1 t p.2.2.1‖ ≤ D) (h : History) :
    ((tilted O μ Lg t D r q).law (p, h)).real
      {z | r < ‖z.1 - P.tiltedResponse p.1 t p.2.2.1‖} ≤ Real.exp (-(q : ℝ) / 8) := by
  exact StatefulConfidence.amplify_confidence_at
    (ParameterizedStatefulAccelerated.tiltedSolve O μ Lg t D (r / 12))
    ((p.1, p.2.2.1), p.2.2.2) (P.tiltedResponse p.1 t p.2.2.1) r hr
    (fun h' => ParameterizedStatefulAccelerated.tiltedSolve_accuracy O P hgy
      p.1 t p.2.2.1 p.2.2.2 D (r / 12) (by positivity) hinit h') q h

omit [FiniteDimensional ℝ Y] [Nontrivial Y] in
theorem gxMean_confidence (hgx : ∀ x y, O.lower.truth_x (x, y) = P.gx x y)
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) [NeZero q] (x : X) (y : Y) (h : History) :
    ((gxMean O δ q).law ((x, y), h)).real
      {z | δ < ‖z.1 - P.gx x y‖} ≤ Real.exp (-(q : ℝ) / 8) := by
  have hb := StatefulConfidence.amplify_confidence_at (O.gx.batchAtRadius (δ / 12))
    (x, y) (O.lower.truth_x (x, y)) δ hδ
    (fun h' => O.gx.batchAtRadius_mse (δ / 12) (by positivity) (x, y) h') q h
  rw [hgx] at hb
  exact hb

end Bilevel.CachedEstimatorProcedure
