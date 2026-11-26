import Bilevel.StatefulAcceleratedSolver
import Bilevel.HistorySFO

/-! The accelerated solver instantiated by the original full-gradient SFO
and an actual primitive lower objective with a frozen linear tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Bilevel.StatefulAccelerated
open Stateful AcceleratedInner

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

/-- Fixing the outer point changes only the query parameterization. The full
joint response and original history update remain intact at every call. -/
def frozenLowerOracle (x : X) :
    HistoryOracle (Query := Y) (History := History) (Obs := FullResponse X Y) (E := Y) σg where
  law := O.law.comap (fun z : Y × History => ((x, z.1), z.2)) (by fun_prop)
  markov := inferInstance
  read := fun z => z.2.2
  read_measurable := by fun_prop
  truth := fun y => O.lower.truth_y (x, y)
  truth_measurable := O.lower.truth_y_measurable.comp (measurable_const.prodMk measurable_id)
  update := fun z => O.update (((x, z.1.1), z.1.2), z.2)
  update_measurable := O.update_measurable.comp (by fun_prop)
  square_integrable := fun y h => O.lower.y_square_integrable (x, y) h
  mean := fun y h => O.lower.mean_y (x, y) h
  variance := fun y h => O.lower.y_variance (x, y) h

def tiltedSolve (μ Lg : ℝ) (x : X) (t : ℝ) (a : Y) (R r : ℝ) : Procedure Y History Y :=
  solve (frozenLowerOracle O x) μ Lg (Real.sqrt (μ / Lg)) (t • a) R r

theorem tiltedSolve_calls (μ Lg : ℝ) (x : X) (t : ℝ) (a : Y) (R r : ℝ) :
    (tiltedSolve O μ Lg x t a R r).CallsEq
      (fun _ => solveCalls μ Lg (Real.sqrt (μ / Lg)) σg R r) :=
  solve_calls (frozenLowerOracle O x) μ Lg (Real.sqrt (μ / Lg)) (t • a) R r

variable {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)
  [FiniteDimensional ℝ Y] [Nontrivial Y]

/-- Actual original-SFO accelerated solve for every fixed outer point and
frozen direction. No minimizer, Hessian product, or stationary sample law is
provided to the algorithm. The target response is constructed from Primitive. -/
theorem tiltedSolve_accuracy (hgy : ∀ x y, O.lower.truth_y (x, y) = P.gy x y)
    (x : X) (t : ℝ) (a initial : Y) (R r : ℝ) (hr : 0 < r)
    (hinit : ‖initial - P.tiltedResponse x t a‖ ≤ R) (h : History) :
    Integrable (fun z => ‖z.1 - P.tiltedResponse x t a‖ ^ 2)
      ((tiltedSolve O μ Lg x t a R r).law (initial, h)) ∧
      (∫ z, ‖z.1 - P.tiltedResponse x t a‖ ^ 2
        ∂(tiltedSolve O μ Lg x t a R r).law (initial, h)) ≤ r ^ 2 := by
  obtain ⟨ha, ha1, hrel⟩ := square_root_parameter P.μ_pos P.strong_convexity_le_smoothness
  have hR : 0 ≤ R := (norm_nonneg _).trans hinit
  apply solve_distance (frozenLowerOracle O x) (P.tiltedLower x t a)
    (fun y => P.gy x y + t • a) (t • a)
    (P.μ_pos.trans_le P.strong_convexity_le_smoothness) P.μ_pos P.strong_convexity_le_smoothness
    ha ha1 hrel
    (fun y => by change O.lower.truth_y (x, y) + t • a = _; rw [hgy])
    (P.tilted_hasGradientAt x t a) _ (P.tilted_strong_convex x t a)
    (P.tiltedResponse x t a) (P.tiltedResponse_minimizes x t a) _ hR hr initial _ h
  · intro y z
    simpa only [add_sub_add_right_eq_sub] using P.gy_lipschitz_y x y z
  · dsimp only
    rw [P.tiltedResponse_stationary, neg_smul]
    exact neg_add_cancel _
  · exact (sq_le_sq₀ (norm_nonneg _) hR).mpr hinit

end Bilevel.StatefulAccelerated
