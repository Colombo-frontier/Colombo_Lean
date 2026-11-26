import Bilevel.ParameterizedStatefulAcceleratedSolver

/-! A single original-SFO accelerated solver kernel with adaptive outer point,
frozen direction, and starting point as jointly measurable inputs. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.ParameterizedStatefulAccelerated
open Stateful AcceleratedInner

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

def tiltedSolve (μ Lg t R r : ℝ) : Procedure ((X × Y) × Y) History Y :=
  solve O.gy (fun z : (X × Y) × Y => (z.1.1, z.2)) (by fun_prop)
    (fun p : X × Y => t • p.2) (by fun_prop) μ Lg (Real.sqrt (μ / Lg)) R r

theorem tiltedSolve_calls (μ Lg t R r : ℝ) :
    (tiltedSolve O μ Lg t R r).CallsEq
      (fun _ => StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ / Lg)) σg R r) :=
  solve_calls O.gy _ _ _ _ μ Lg (Real.sqrt (μ / Lg)) R r

variable {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)
  [FiniteDimensional ℝ Y] [Nontrivial Y]

theorem tiltedSolve_accuracy (hgy : ∀ x y, O.lower.truth_y (x, y) = P.gy x y)
    (x : X) (t : ℝ) (a initial : Y) (R r : ℝ) (hr : 0 < r)
    (hinit : ‖initial - P.tiltedResponse x t a‖ ≤ R) (h : History) :
    Integrable (fun z => ‖z.1 - P.tiltedResponse x t a‖ ^ 2)
      ((tiltedSolve O μ Lg t R r).law (((x, a), initial), h)) ∧
      (∫ z, ‖z.1 - P.tiltedResponse x t a‖ ^ 2
        ∂(tiltedSolve O μ Lg t R r).law (((x, a), initial), h)) ≤ r ^ 2 := by
  obtain ⟨ha, ha1, hrel⟩ := square_root_parameter P.μ_pos P.strong_convexity_le_smoothness
  have hR : 0 ≤ R := (norm_nonneg _).trans hinit
  apply solve_distance O.gy _ _ _ _ (P.tiltedLower x t a) (fun y => P.gy x y + t • a)
    (P.μ_pos.trans_le P.strong_convexity_le_smoothness) P.μ_pos P.strong_convexity_le_smoothness
    ha ha1 hrel (x, a)
    (fun y => by change O.lower.truth_y (x, y) + t • a = _; rw [hgy])
    (P.tilted_hasGradientAt x t a) _ (P.tilted_strong_convex x t a)
    (P.tiltedResponse x t a) (P.tiltedResponse_minimizes x t a) _ hR hr initial _ h
  · intro y z
    simpa only [add_sub_add_right_eq_sub] using P.gy_lipschitz_y x y z
  · dsimp only
    rw [P.tiltedResponse_stationary, neg_smul]
    exact neg_add_cancel _
  · exact (sq_le_sq₀ (norm_nonneg _) hR).mpr hinit

/-- Arbitrary measurable adaptive inputs may be supplied to this single
kernel. The only domain requirement is the public initialization certificate. -/
theorem tiltedSolve_reparam_mse {Input : Type*} [MeasurableSpace Input]
    (hgy : ∀ x y, O.lower.truth_y (x, y) = P.gy x y)
    (t R r : ℝ) (hr : 0 < r) (input : Input → (X × Y) × Y) (hi : Measurable input)
    (hinit : ∀ p, ‖(input p).2 - P.tiltedResponse (input p).1.1 t (input p).1.2‖ ≤ R) :
    ((tiltedSolve O μ Lg t R r).reparam input hi).MSEBound
      (fun p => P.tiltedResponse (input p).1.1 t (input p).1.2) (fun _ => r) := by
  intro p h
  exact tiltedSolve_accuracy O P hgy (input p).1.1 t (input p).1.2 (input p).2 R r hr (hinit p) h

end Bilevel.ParameterizedStatefulAccelerated
