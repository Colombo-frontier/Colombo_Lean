import Problem254
import Mathlib.MeasureTheory.Integral.IntegrableOn

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Paper254

theorem ball_coordinate_bound {d : ℕ} (w : (ballDomain d).carrier) (j : Fin d) : |w.val j| ≤ (1/2 : ℝ) := by
  have hw : ‖w.val‖ ≤ (1/2 : ℝ) := by simpa [ballDomain,Metric.mem_closedBall] using w.property
  have hj := PiLp.norm_apply_le w.val j
  simpa only [Real.norm_eq_abs] using hj.trans hw

theorem coordinateSquare_nonneg {d : ℕ} (j : Fin d) (y : Bool) (w : Space d) :
    0 ≤ coordinateSquare j y w := by unfold coordinateSquare; positivity

theorem coordinateSquare_bound {d : ℕ} (j : Fin d) (y : Bool) (w : (ballDomain d).carrier) :
    ‖coordinateSquare j y w.val‖ ≤ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (coordinateSquare_nonneg j y w.val)]
  have hw := abs_le.mp (ball_coordinate_bound w j)
  unfold coordinateSquare
  cases y <;> simp only [Bool.false_eq_true, if_false, if_true] <;> nlinarith

theorem coordinateSquare_continuous {d : ℕ} (j : Fin d) (y : Bool) :
    Continuous (coordinateSquare j y) := by
  unfold coordinateSquare
  exact (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).sub continuous_const).pow 2).div_const 2

theorem hard_regret_integrable {d T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → OnlineLearner (ballDomain d) T)
    (hA : SeedMeasurable A) (s : Fin T → Fin d × Bool) (u : Fin T → (ballDomain d).carrier) :
    Integrable (fun ω => regret (A ω) (hardSequence s) u) μ := by
  unfold regret
  apply integrable_finset_sum
  intro t _
  have hm : Measurable (fun ω => hardSequence s t (predictions (A ω) (hardSequence s) t).val) :=
    (coordinateSquare_continuous (s t).1 (s t).2).measurable.comp (hA t (past (hardSequence s) t))
  have hi : Integrable (fun ω => hardSequence s t (predictions (A ω) (hardSequence s) t).val) μ :=
    Integrable.of_bound hm.aestronglyMeasurable 2 (Filter.Eventually.of_forall (fun ω =>
      coordinateSquare_bound (s t).1 (s t).2 (predictions (A ω) (hardSequence s) t)))
  exact hi.sub (integrable_const _)

end Paper254
#print axioms Paper254.hard_regret_integrable
