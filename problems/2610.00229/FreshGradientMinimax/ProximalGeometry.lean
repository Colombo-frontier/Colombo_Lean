import FreshGradientMinimax.Objective
import FreshGradientMinimax.Calculus
import FreshGradientMinimax.Proximal
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-! The actual proximal point of an NC--SC value function. This discharges the
existence and first-order supporting premises of the earlier proximal lemmas.
No inner algorithm or complexity bound is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
namespace NCObjective
variable {dx dy : ℕ} {L μ : ℝ} (O : NCObjective dx dy L μ)

/-- The L-weak-convexity supporting inequality for the true primal value. -/
theorem value_weak_support (x z : Euclid dx) :
    O.value x + ⟪O.primalGradient x, z - x⟫_ℝ - L / 2 * ‖z - x‖ ^ 2 ≤ O.value z := by
  have h := smooth_taylor_remainder (fun t => O.derivative_x t (O.dualMax x))
    (fun t t' => O.gradX_lip_primal t t' (O.dualMax x)) x (z - x)
  rw [add_sub_cancel, ← O.value_eq_max x] at h
  have hl := (abs_le.mp h).1
  have hv := O.le_value z (O.dualMax x)
  unfold primalGradient
  linarith

def proxGradient (c x : Euclid dx) : Euclid dx := O.primalGradient x + (2 * L) • (x - c)

theorem prox_hasFDerivAt (c x : Euclid dx) :
    HasFDerivAt (proximalValue O.value L c) (innerSL ℝ (O.proxGradient c x)) x := by
  have hn := (hasStrictFDerivAt_norm_sq (x - c)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const c)
  convert (O.value_hasFDerivAt x).add (hn.const_mul L) using 1
  ext h
  simp [proxGradient, innerSL_apply, inner_add_left, real_inner_smul_left]
  ring

theorem prox_strong_support (c x z : Euclid dx) :
    proximalValue O.value L c x + ⟪O.proxGradient c x, z - x⟫_ℝ + L / 2 * ‖z - x‖ ^ 2 ≤
      proximalValue O.value L c z := by
  have hw := O.value_weak_support x z
  have he : ‖z - c‖ ^ 2 = ‖x - c‖ ^ 2 + 2 * ⟪x - c, z - x⟫_ℝ + ‖z - x‖ ^ 2 := by
    rw [show z - c = (x - c) + (z - x) by abel, norm_add_sq_real]
  have heL := congrArg (fun t : ℝ => L * t) he
  dsimp only at heL
  simp only [proximalValue, proxGradient, inner_add_left, real_inner_smul_left]
  nlinarith only [hw, heL]

theorem prox_minimum_exists (c : Euclid dx) :
    ∃ u, ∀ x, proximalValue O.value L c u ≤ proximalValue O.value L c x := by
  have hc : StrongConcaveGradient (fun x => -proximalValue O.value L c x)
      (fun x => -O.proxGradient c x) L := by
    intro x z
    have h := O.prox_strong_support c x z
    simp only [inner_neg_left]
    linarith
  have hf : Continuous (fun x => -proximalValue O.value L c x) := by
    exact (continuous_iff_continuousAt.mpr (fun x => (O.prox_hasFDerivAt c x).continuousAt)).neg
  obtain ⟨u, hu⟩ := strong_concave_maximum_exists O.L_pos hc hf
  exact ⟨u, fun x => neg_le_neg_iff.mp (hu x)⟩

def proxPoint (c : Euclid dx) : Euclid dx := Classical.choose (O.prox_minimum_exists c)

theorem proxPoint_minimizes (c x : Euclid dx) :
    proximalValue O.value L c (O.proxPoint c) ≤ proximalValue O.value L c x :=
  Classical.choose_spec (O.prox_minimum_exists c) x

theorem prox_gradient_zero (c : Euclid dx) : O.proxGradient c (O.proxPoint c) = 0 := by
  have hmin : IsLocalMin (proximalValue O.value L c) (O.proxPoint c) :=
    Filter.Eventually.of_forall (O.proxPoint_minimizes c)
  have hd := hmin.hasFDerivAt_eq_zero (O.prox_hasFDerivAt c (O.proxPoint c))
  have hv := congrArg (fun l : Euclid dx →L[ℝ] ℝ => l (O.proxGradient c (O.proxPoint c))) hd
  simp only [innerSL_apply, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at hv
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (O.proxGradient c (O.proxPoint c))]

theorem proxPoint_unique (c u : Euclid dx)
    (hu : ∀ x, proximalValue O.value L c u ≤ proximalValue O.value L c x) : u = O.proxPoint c := by
  have h := O.prox_strong_support c (O.proxPoint c) u
  rw [O.prox_gradient_zero, inner_zero_left, add_zero] at h
  have hu' := hu (O.proxPoint c)
  have hsq : L / 2 * ‖u - O.proxPoint c‖ ^ 2 ≤ 0 := by linarith
  have hsq' : ‖u - O.proxPoint c‖ ^ 2 ≤ 0 :=
    (mul_le_mul_left (show 0 < L / 2 from div_pos O.L_pos (by norm_num))).mp (by simpa using hsq)
  have hn : ‖u - O.proxPoint c‖ = 0 := by nlinarith [norm_nonneg (u - O.proxPoint c)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem prox_primal_gradient_identity (c : Euclid dx) :
    O.primalGradient (O.proxPoint c) = proximalResidual L c (O.proxPoint c) := by
  have hz := O.prox_gradient_zero c
  unfold proxGradient at hz
  calc
    O.primalGradient (O.proxPoint c) = -((2 * L) • (O.proxPoint c - c)) :=
      eq_neg_of_add_eq_zero_left hz
    _ = _ := by unfold proximalResidual; module

theorem prox_decrease (c : Euclid dx) :
    ‖proximalResidual L c (O.proxPoint c)‖ ^ 2 / (8 * L) ≤
      O.value c - proximalValue O.value L c (O.proxPoint c) := by
  apply proximal_decrease O.L_pos
  have h := O.prox_strong_support c (O.proxPoint c) c
  simpa only [O.prox_gradient_zero, inner_zero_left, add_zero] using h

theorem inexact_prox_descent (c x : Euclid dx) {η : ℝ}
    (hgap : proximalValue O.value L c x ≤ proximalValue O.value L c (O.proxPoint c) + η) :
    O.value x + L * ‖x - c‖ ^ 2 ≤
      O.value c - ‖proximalResidual L c (O.proxPoint c)‖ ^ 2 / (8 * L) + η := by
  apply inexact_proximal_step O.L_pos c (O.proxPoint c) x _ hgap
  have h := O.prox_strong_support c (O.proxPoint c) c
  simpa only [O.prox_gradient_zero, inner_zero_left, add_zero] using h

theorem proxGradient_lip (c x z : Euclid dx) :
    ‖O.proxGradient c x - O.proxGradient c z‖ ≤ (3 + L / μ) * L * ‖x - z‖ := by
  have hL := O.L_pos
  have ht := norm_add_le (O.primalGradient x - O.primalGradient z) ((2 * L) • (x - z))
  have he : O.proxGradient c x - O.proxGradient c z =
      (O.primalGradient x - O.primalGradient z) + (2 * L) • (x - z) := by
    unfold proxGradient
    module
  rw [he]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * L)] at ht
  have h := O.primalGradient_lip x z
  linarith

theorem proxGradient_lip_four_kappa (c x z : Euclid dx) :
    ‖O.proxGradient c x - O.proxGradient c z‖ ≤ 4 * (L / μ) * L * ‖x - z‖ := by
  have hk : 1 ≤ L / μ := (le_div_iff₀ O.μ_pos).mpr (by simpa using O.μ_le_L)
  have h := O.proxGradient_lip c x z
  have hc : (3 + L / μ) * L ≤ 4 * (L / μ) * L := by nlinarith [O.L_pos]
  exact h.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

theorem prox_residual_distance (c x : Euclid dx) :
    L * ‖x - O.proxPoint c‖ ≤ ‖O.proxGradient c x‖ := by
  have hc : StrongConcaveGradient (fun x => -proximalValue O.value L c x)
      (fun x => -O.proxGradient c x) L := by
    intro a b
    have h := O.prox_strong_support c a b
    simp only [inner_neg_left]
    linarith
  have hm := strong_concave_gradient_monotone hc x (O.proxPoint c)
  simp only [O.prox_gradient_zero, neg_zero, zero_sub, neg_neg] at hm
  exact residual_controls_distance L (O.proxGradient c x) (x - O.proxPoint c) hm

theorem prox_gradient_sq_le_gap (c x : Euclid dx) :
    ‖O.proxGradient c x‖ ^ 2 ≤ 8 * (L / μ) * L *
      (proximalValue O.value L c x - proximalValue O.value L c (O.proxPoint c)) := by
  have hp : 0 < 4 * (L / μ) * L := by have := O.L_pos; have := O.μ_pos; positivity
  have h := smooth_gradient_sq_le_gap hp (O.prox_hasFDerivAt c)
    (O.proxGradient_lip_four_kappa c) (O.proxPoint c) (O.proxPoint_minimizes c) x
  convert h using 1
  ring

/-- The constant 18 now applies to the actual gradient of the primal value. -/
theorem true_gradient_from_prox (c x : Euclid dx) :
    ‖gradient O.value x‖ ^ 2 ≤ 2 * ‖proximalResidual L c (O.proxPoint c)‖ ^ 2 +
      18 * ‖O.proxGradient c x‖ ^ 2 := by
  rw [O.true_primal_gradient]
  apply true_gradient_sq_bound O.L_pos.le _ _ _ _
    (primal_gradient_identity c (O.proxPoint c) x (O.primalGradient x))
  exact O.prox_residual_distance c x

end NCObjective
end FreshGradientMinimax
