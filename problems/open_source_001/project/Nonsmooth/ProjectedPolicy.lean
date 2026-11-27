import Nonsmooth.Minimax
import Nonsmooth.MeasurableSimulation
import Nonsmooth.BallProjection

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

abbrev ProjectedState (E : Type) [NormedAddCommGroup E] (q : ℝ) :=
  Feasible E q × Feasible E q × ℕ

def meanPoint (q : ℝ) (n : ℕ) (a x : Feasible E q) : Feasible E q :=
  ⟨((n : ℝ) / (n + 1)) • a.val + (1 / ((n : ℝ) + 1)) • x.val, by
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hw : (n : ℝ) / (n + 1) + 1 / ((n : ℝ) + 1) = 1 := by field_simp
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (convex_closedBall (0 : E) q) (by simpa using a.property) (by simpa using x.property)
        (div_nonneg (Nat.cast_nonneg n) hn.le) (by positivity : 0 ≤ 1 / ((n : ℝ) + 1)) hw⟩

def projectPoint (q : ℝ) (hq : 0 ≤ q) (x : E) : Feasible E q :=
  ⟨ballProject q x, ballProject_feasible hq x⟩

theorem projectPoint_measurable {q : ℝ} (hq : 0 ≤ q) : Measurable (projectPoint (E := E) q hq) := by
  apply Measurable.subtype_mk
  exact (ballProject_lipschitz hq).continuous.measurable

theorem meanPoint_measurable (q : ℝ) :
    Measurable (fun z : ℕ × Feasible E q × Feasible E q => meanPoint q z.1 z.2.1 z.2.2) := by
  apply Measurable.subtype_mk
  try dsimp only [meanPoint]
  fun_prop

end
end Nonsmooth
