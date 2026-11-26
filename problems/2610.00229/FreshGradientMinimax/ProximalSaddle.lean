import FreshGradientMinimax.ProximalGeometry
import FreshGradientMinimax.SaddleGeometry

/-! The proximal objective is an actual SCSC objective with joint smoothness 3L.
Its saddle is identified with the proximal point, and its genuine max--min gap
controls primal suboptimality. This is the analytic reduction used in G.1. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
namespace NCObjective
variable {dx dy : ℕ} {L μ : ℝ} (O : NCObjective dx dy L μ)

def regularizedF (c u : Euclid dx) (v : Euclid dy) : ℝ := O.f u v + L * ‖u - c‖ ^ 2
def regularizedX (c u : Euclid dx) (v : Euclid dy) : Euclid dx :=
  O.gradX u v + (2 * L) • (u - c)

theorem regularized_derivative (c : Euclid dx) (z : Joint dx dy) :
    HasFDerivAt (fun w : Joint dx dy => O.regularizedF c w.1 w.2)
      ((innerSL ℝ (O.regularizedX c z.1 z.2)).coprod (innerSL ℝ (O.gradY z.1 z.2))) z := by
  have hn := (hasStrictFDerivAt_norm_sq (z.1 - c)).hasFDerivAt.comp z
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).sub_const c)
  apply ((O.derivative z).add (hn.const_mul L)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  simp [regularizedX, inner_add_left, real_inner_smul_left]
  ring

theorem regularized_joint_smooth (c u u' : Euclid dx) (v v' : Euclid dy) :
    ‖O.regularizedX c u v - O.regularizedX c u' v'‖ ^ 2 +
        ‖O.gradY u v - O.gradY u' v'‖ ^ 2 ≤
      (3 * L) ^ 2 * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2) := by
  have hL := O.L_pos
  have he : O.regularizedX c u v - O.regularizedX c u' v' =
      (O.gradX u v - O.gradX u' v') + (2 * L) • (u - u') := by
    unfold regularizedX
    module
  rw [he]
  have ht := norm_add_le (O.gradX u v - O.gradX u' v') ((2 * L) • (u - u'))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * L)] at ht
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity :
    0 ≤ ‖O.gradX u v - O.gradX u' v'‖ + 2 * L * ‖u - u'‖)).mpr ht
  have hx : ‖(O.gradX u v - O.gradX u' v') + (2 * L) • (u - u')‖ ^ 2 ≤
      3 * ‖O.gradX u v - O.gradX u' v'‖ ^ 2 + 6 * L ^ 2 * ‖u - u'‖ ^ 2 := by
    nlinarith only [hsq, sq_nonneg (‖O.gradX u v - O.gradX u' v'‖ - L * ‖u - u'‖)]
  have hj := mul_le_mul_of_nonneg_left (O.joint_smooth u v u' v') (show (0 : ℝ) ≤ 3 by norm_num)
  have hy := sq_nonneg ‖O.gradY u v - O.gradY u' v'‖
  have hv := mul_nonneg (sq_nonneg L) (sq_nonneg ‖v - v'‖)
  nlinarith only [hx, hj, hy, hv]

theorem regularized_primal_strong (c : Euclid dx) (v : Euclid dy) :
    StrongConvexGradient (fun u => O.regularizedF c u v) (fun u => O.regularizedX c u v) L := by
  intro x z
  have hw := (abs_le.mp (smooth_taylor_remainder (fun t => O.derivative_x t v)
    (fun t t' => O.gradX_lip_primal t t' v) x (z - x))).1
  rw [add_sub_cancel] at hw
  have he : ‖z - c‖ ^ 2 = ‖x - c‖ ^ 2 + 2 * ⟪x - c, z - x⟫_ℝ + ‖z - x‖ ^ 2 := by
    rw [show z - c = (x - c) + (z - x) by abel, norm_add_sq_real]
  have heL := congrArg (fun t : ℝ => L * t) he
  dsimp only at heL
  simp only [regularizedF, regularizedX, inner_add_left, real_inner_smul_left]
  nlinarith only [hw, heL]

theorem regularized_dual_strong (c u : Euclid dx) :
    StrongConcaveGradient (O.regularizedF c u) (O.gradY u) μ := by
  intro v w
  have h := O.dual_strong u v w
  unfold regularizedF
  linarith

def proximalObjective (c : Euclid dx) : SCObjective dx dy (3 * L) μ L where
  μ_pos := O.μ_pos
  μ_le_L := by have := O.μ_le_L; have := O.L_pos; linarith
  f := O.regularizedF c
  gradX := O.regularizedX c
  gradY := O.gradY
  derivative := O.regularized_derivative c
  joint_smooth := fun u v u' v' => O.regularized_joint_smooth c u u' v v'
  dual_strong := O.regularized_dual_strong c
  α_pos := O.L_pos
  primal_strong := O.regularized_primal_strong c

theorem proximalObjective_dualMax (c u : Euclid dx) :
    (O.proximalObjective c).toNCObjective.dualMax u = O.dualMax u := by
  symm
  apply (O.proximalObjective c).toNCObjective.dualMax_unique
  intro v
  change O.f u v + L * ‖u - c‖ ^ 2 ≤ O.f u (O.dualMax u) + L * ‖u - c‖ ^ 2
  exact add_le_add_right (O.le_dualMax u v) _

theorem proximalObjective_value (c u : Euclid dx) :
    (O.proximalObjective c).toNCObjective.value u = proximalValue O.value L c u := by
  rw [(O.proximalObjective c).toNCObjective.value_eq_max, O.proximalObjective_dualMax]
  change O.f u (O.dualMax u) + L * ‖u - c‖ ^ 2 = O.value u + L * ‖u - c‖ ^ 2
  rw [O.value_eq_max]

theorem proximalObjective_saddleU (c : Euclid dx) : (O.proximalObjective c).saddleU = O.proxPoint c := by
  apply O.proxPoint_unique
  intro u
  simpa only [O.proximalObjective_value] using (O.proximalObjective c).saddleU_minimizes u

theorem proximalObjective_saddleV (c : Euclid dx) :
    (O.proximalObjective c).saddleV = O.dualMax (O.proxPoint c) := by
  rw [SCObjective.saddleV, O.proximalObjective_dualMax, O.proximalObjective_saddleU]

theorem proximal_gap_dominates_value (c u : Euclid dx) (v : Euclid dy) :
    proximalValue O.value L c u - proximalValue O.value L c (O.proxPoint c) ≤
      (O.proximalObjective c).gap u v := by
  simpa only [O.proximalObjective_value, O.proximalObjective_saddleU] using
    (O.proximalObjective c).gap_dominates_primal u v

theorem proximal_gap_descent (c u : Euclid dx) (v : Euclid dy) :
    O.value u + L * ‖u - c‖ ^ 2 ≤
      O.value c - ‖proximalResidual L c (O.proxPoint c)‖ ^ 2 / (8 * L) +
        (O.proximalObjective c).gap u v := by
  apply O.inexact_prox_descent
  have h := O.proximal_gap_dominates_value c u v
  linarith

theorem proximal_gap_controls_distance (c u : Euclid dx) (v : Euclid dy) :
    L * ‖u - O.proxPoint c‖ ^ 2 + μ * ‖v - O.dualMax (O.proxPoint c)‖ ^ 2 ≤
      2 * (O.proximalObjective c).gap u v := by
  simpa only [O.proximalObjective_saddleU, O.proximalObjective_saddleV] using
    (O.proximalObjective c).gap_controls_distance u v

end NCObjective
end FreshGradientMinimax
