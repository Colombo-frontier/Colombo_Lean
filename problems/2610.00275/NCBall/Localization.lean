import NCBall.Goldstein
import Mathlib.Tactic

/-! # Path and output localization from clipped increments (Section 11)

Only the deterministic path bound is proved. This file does not claim the
Kornowski--Shamir convergence theorem or its stochastic estimator analysis.
-/

noncomputable section
open Set Metric
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem clipped_path_bound {D : ℝ} (x : ℕ → E) (T : ℕ)
    (hstep : ∀ t < T, ‖x (t + 1) - x t‖ ≤ D) :
    ∀ t ≤ T, ‖x t - x 0‖ ≤ (t : ℝ) * D := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    intro ht
    have hp := ih (by omega)
    have hs := hstep t (by omega)
    have htri : ‖x (t + 1) - x 0‖ ≤ ‖x (t + 1) - x t‖ + ‖x t - x 0‖ := by
      calc
        _ = ‖(x (t + 1) - x t) + (x t - x 0)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    push_cast
    linarith

omit [NormedSpace ℝ E] in
theorem perturbation_bound {a x v : E} {r ρ : ℝ}
    (hx : ‖x - a‖ ≤ r) (hv : ‖v‖ ≤ ρ) :
    ‖x + v - a‖ ≤ r + ρ := by
  have heq : x + v - a = (x - a) + v := by abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hx hv)

theorem averaged_output_in_ball {a : E} {r : ℝ} {S : Set E}
    (hS : S ⊆ closedBall a r) :
    closedConvexHull ℝ S ⊆ closedBall a r :=
  closedConvexHull_min hS (convex_closedBall a r) isClosed_closedBall

/-- Elementary norm estimate used in (7.11). It applies once the analytic
gradient bound for a local bump has been established. -/
theorem carrier_perturbation_nonstationary {e b : E} {η : ℝ}
    (hη : 0 < η) (he : ‖e‖ = 1) (hb : ‖b‖ ≤ (4 * η) / 8) :
    η < ‖-(4 * η) • e + b‖ := by
  have hc : ‖-(4 * η) • e‖ = 4 * η := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity), he, mul_one]
  have htri : ‖-(4 * η) • e‖ ≤ ‖-(4 * η) • e + b‖ + ‖b‖ := by
    calc
      _ = ‖(-(4 * η) • e + b) - b‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖-(4 * η) • e + b‖ + ‖b‖ := norm_sub_le _ _
  rw [hc] at htri
  linarith

end NCBall
