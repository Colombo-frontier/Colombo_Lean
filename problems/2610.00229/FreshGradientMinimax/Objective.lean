import FreshGradientMinimax.DualGeometry
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Finite-dimensional NC--SC objectives, their actual maximizing dual point,
and the true derivative of the primal value function. Joint smoothness uses the
Euclidean sum of squared component norms, not the default max product norm.
No oracle bound or algorithmic conclusion is an instance field. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

abbrev Euclid (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Joint (dx dy : ℕ) := Euclid dx × Euclid dy

def jointNormSq {dx dy : ℕ} (z : Joint dx dy) : ℝ := ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2

structure NCObjective (dx dy : ℕ) (L μ : ℝ) where
  μ_pos : 0 < μ
  μ_le_L : μ ≤ L
  f : Euclid dx → Euclid dy → ℝ
  gradX : Euclid dx → Euclid dy → Euclid dx
  gradY : Euclid dx → Euclid dy → Euclid dy
  derivative : ∀ z : Joint dx dy, HasFDerivAt (fun w : Joint dx dy => f w.1 w.2)
    ((innerSL ℝ (gradX z.1 z.2)).coprod (innerSL ℝ (gradY z.1 z.2))) z
  joint_smooth : ∀ x y x' y',
    ‖gradX x y - gradX x' y'‖ ^ 2 + ‖gradY x y - gradY x' y'‖ ^ 2 ≤
      L ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)
  dual_strong : ∀ x, StrongConcaveGradient (f x) (gradY x) μ

namespace NCObjective
variable {dx dy : ℕ} {L μ : ℝ} (O : NCObjective dx dy L μ)

theorem L_pos (O : NCObjective dx dy L μ) : 0 < L := O.μ_pos.trans_le O.μ_le_L

theorem derivative_x (x : Euclid dx) (y : Euclid dy) :
    HasFDerivAt (fun t => O.f t y) (innerSL ℝ (O.gradX x y)) x := by
  have hm : HasFDerivAt (fun t : Euclid dx => (t, y))
      ((ContinuousLinearMap.id ℝ (Euclid dx)).prod 0) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)
  have hd := (O.derivative (x, y)).comp x hm
  convert hd using 1
  ext h
  simp

theorem derivative_y (x : Euclid dx) (y : Euclid dy) :
    HasFDerivAt (O.f x) (innerSL ℝ (O.gradY x y)) y := by
  convert (O.derivative (x, y)).comp y
    ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)) using 1
  ext h
  simp

theorem dual_maximum_exists (x : Euclid dx) : ∃ y, ∀ z, O.f x z ≤ O.f x y := by
  exact strong_concave_maximum_exists O.μ_pos (O.dual_strong x)
    (continuous_iff_continuousAt.mpr (fun y => (O.derivative_y x y).continuousAt))

def dualMax (x : Euclid dx) : Euclid dy := Classical.choose (O.dual_maximum_exists x)

theorem le_dualMax (x : Euclid dx) (y : Euclid dy) : O.f x y ≤ O.f x (O.dualMax x) :=
  Classical.choose_spec (O.dual_maximum_exists x) y

theorem dualMax_unique (x : Euclid dx) (y : Euclid dy) (hy : ∀ z, O.f x z ≤ O.f x y) :
    y = O.dualMax x :=
  strong_concave_maximum_unique O.μ_pos (O.dual_strong x) (O.derivative_y x)
    y (O.dualMax x) hy (O.le_dualMax x)

theorem dual_gradient_zero (x : Euclid dx) : O.gradY x (O.dualMax x) = 0 :=
  gradient_zero_at_global_max (O.dualMax x) (O.derivative_y x (O.dualMax x)) (O.le_dualMax x)

def value (x : Euclid dx) : ℝ := sSup (Set.range (O.f x))

theorem value_eq_max (x : Euclid dx) : O.value x = O.f x (O.dualMax x) := by
  apply IsGreatest.csSup_eq
  exact ⟨⟨O.dualMax x, rfl⟩, by rintro _ ⟨y, rfl⟩; exact O.le_dualMax x y⟩

theorem le_value (x : Euclid dx) (y : Euclid dy) : O.f x y ≤ O.value x := by
  rw [O.value_eq_max]
  exact O.le_dualMax x y

theorem gradX_lip_primal (x x' : Euclid dx) (y : Euclid dy) :
    ‖O.gradX x y - O.gradX x' y‖ ≤ L * ‖x - x'‖ := by
  have h := O.joint_smooth x y x' y
  simp only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at h
  have hp := O.L_pos
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hp.le (norm_nonneg _))).mp
  rw [mul_pow]
  linarith [sq_nonneg ‖O.gradY x y - O.gradY x' y‖]

theorem gradX_lip_dual (x : Euclid dx) (y y' : Euclid dy) :
    ‖O.gradX x y - O.gradX x y'‖ ≤ L * ‖y - y'‖ := by
  have h := O.joint_smooth x y x y'
  simp only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] at h
  have hp := O.L_pos
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hp.le (norm_nonneg _))).mp
  rw [mul_pow]
  linarith [sq_nonneg ‖O.gradY x y - O.gradY x y'‖]

theorem gradY_lip_primal (x x' : Euclid dx) (y : Euclid dy) :
    ‖O.gradY x y - O.gradY x' y‖ ≤ L * ‖x - x'‖ := by
  have h := O.joint_smooth x y x' y
  simp only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at h
  have hp := O.L_pos
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hp.le (norm_nonneg _))).mp
  rw [mul_pow]
  linarith [sq_nonneg ‖O.gradX x y - O.gradX x' y‖]

theorem gradY_lip_dual (x : Euclid dx) (y y' : Euclid dy) :
    ‖O.gradY x y - O.gradY x y'‖ ≤ L * ‖y - y'‖ := by
  have h := O.joint_smooth x y x y'
  simp only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] at h
  have hp := O.L_pos
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hp.le (norm_nonneg _))).mp
  rw [mul_pow]
  linarith [sq_nonneg ‖O.gradX x y - O.gradX x y'‖]

theorem residual_distance (x : Euclid dx) (y : Euclid dy) :
    μ * ‖y - O.dualMax x‖ ≤ ‖O.gradY x y‖ ∧
      ‖O.gradY x y‖ ≤ L * ‖y - O.dualMax x‖ :=
  dual_residual_distance_bounds (O.dual_strong x) (O.dualMax x)
    (O.dual_gradient_zero x) (O.gradY_lip_dual x) y

theorem dualMax_lip (x x' : Euclid dx) :
    ‖O.dualMax x - O.dualMax x'‖ ≤ (L / μ) * ‖x - x'‖ := by
  have hl := (O.residual_distance x (O.dualMax x')).1
  have hu := O.gradY_lip_primal x x' (O.dualMax x')
  rw [O.dual_gradient_zero x', sub_zero] at hu
  rw [norm_sub_rev] at hl
  have h : μ * ‖O.dualMax x - O.dualMax x'‖ ≤ L * ‖x - x'‖ := hl.trans hu
  have h' := (le_div_iff₀ O.μ_pos).mpr (by nlinarith :
    ‖O.dualMax x - O.dualMax x'‖ * μ ≤ L * ‖x - x'‖)
  convert h' using 1
  ring

theorem dualMax_continuous : Continuous O.dualMax := by
  have hp : 0 ≤ L / μ := div_nonneg O.L_pos.le O.μ_pos.le
  apply (show LipschitzWith ⟨L / μ, hp⟩ O.dualMax from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro x x'
  simpa only [dist_eq_norm, NNReal.coe_mk] using O.dualMax_lip x x'

def primalGradient (x : Euclid dx) : Euclid dx := O.gradX x (O.dualMax x)
def jointGradient (z : Joint dx dy) : Joint dx dy := (O.gradX z.1 z.2, O.gradY z.1 z.2)

theorem gradX_joint_bound (z w : Joint dx dy) :
    ‖O.gradX z.1 z.2 - O.gradX w.1 w.2‖ ≤ 2 * L * ‖z - w‖ := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (O.gradX z.1 z.2)
    (O.gradX w.1 z.2) (O.gradX w.1 w.2)
  have hx := O.gradX_lip_primal z.1 w.1 z.2
  have hy := O.gradX_lip_dual w.1 z.2 w.2
  have hp := O.L_pos
  have h1 : ‖z.1 - w.1‖ ≤ ‖z - w‖ := le_max_left _ _
  have h2 : ‖z.2 - w.2‖ ≤ ‖z - w‖ := le_max_right _ _
  nlinarith

theorem gradY_joint_bound (z w : Joint dx dy) :
    ‖O.gradY z.1 z.2 - O.gradY w.1 w.2‖ ≤ 2 * L * ‖z - w‖ := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (O.gradY z.1 z.2)
    (O.gradY w.1 z.2) (O.gradY w.1 w.2)
  have hx := O.gradY_lip_primal z.1 w.1 z.2
  have hy := O.gradY_lip_dual w.1 z.2 w.2
  have hp := O.L_pos
  have h1 : ‖z.1 - w.1‖ ≤ ‖z - w‖ := le_max_left _ _
  have h2 : ‖z.2 - w.2‖ ≤ ‖z - w‖ := le_max_right _ _
  nlinarith

theorem jointGradient_continuous : Continuous O.jointGradient := by
  have hp : 0 ≤ 2 * L := by have := O.L_pos; positivity
  have hx : LipschitzWith ⟨2 * L, hp⟩ (fun z : Joint dx dy => O.gradX z.1 z.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [dist_eq_norm, NNReal.coe_mk] using O.gradX_joint_bound z w
  have hy : LipschitzWith ⟨2 * L, hp⟩ (fun z : Joint dx dy => O.gradY z.1 z.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [dist_eq_norm, NNReal.coe_mk] using O.gradY_joint_bound z w
  exact hx.continuous.prodMk hy.continuous

theorem primalGradient_lip (x x' : Euclid dx) :
    ‖O.primalGradient x - O.primalGradient x'‖ ≤ (1 + L / μ) * L * ‖x - x'‖ := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (O.gradX x (O.dualMax x))
    (O.gradX x' (O.dualMax x)) (O.gradX x' (O.dualMax x'))
  have hx := O.gradX_lip_primal x x' (O.dualMax x)
  have hy := O.gradX_lip_dual x' (O.dualMax x) (O.dualMax x')
  have hys := O.dualMax_lip x x'
  have hp := O.L_pos
  unfold primalGradient
  nlinarith

theorem primalGradient_continuous : Continuous O.primalGradient := by
  have h : Continuous (fun x => (x, O.dualMax x)) := continuous_id.prodMk O.dualMax_continuous
  exact (continuous_fst.comp O.jointGradient_continuous).comp h

/-- Danskin's identity proved using the joint derivative and the Lipschitz
maximizer. Differentiability of the maximizer map is not assumed. -/
theorem value_hasFDerivAt (x : Euclid dx) :
    HasFDerivAt O.value (innerSL ℝ (O.primalGradient x)) x := by
  let lift : Euclid dx → Joint dx dy := fun t => (t, O.dualMax t)
  have hlift : Continuous lift := continuous_id.prodMk O.dualMax_continuous
  have ho := (O.derivative (lift x)).isLittleO.comp_tendsto hlift.continuousAt
  have hb : (fun t => lift t - lift x) =O[nhds x] (fun t => t - x) := by
    apply Asymptotics.IsBigO.of_bound (1 + L / μ)
    apply Filter.Eventually.of_forall
    intro t
    change max ‖t - x‖ ‖O.dualMax t - O.dualMax x‖ ≤ (1 + L / μ) * ‖t - x‖
    apply max_le
    · have hp : 0 ≤ L / μ := div_nonneg O.L_pos.le O.μ_pos.le
      nlinarith [norm_nonneg (t - x)]
    · have h := O.dualMax_lip t x
      nlinarith [norm_nonneg (t - x)]
  have h := ho.trans_isBigO hb
  apply HasFDerivAtFilter.of_isLittleO
  simpa only [lift, Function.comp_def, Prod.fst_sub, Prod.snd_sub,
    ContinuousLinearMap.coprod_apply, innerSL_apply, O.dual_gradient_zero,
    inner_zero_left, add_zero, ← O.value_eq_max, primalGradient] using h

theorem true_primal_gradient (x : Euclid dx) : gradient O.value x = O.primalGradient x := by
  have hg : HasGradientAt O.value (O.primalGradient x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact O.value_hasFDerivAt x
  exact hg.gradient

def PrimalGapAtMost (Δ : ℝ) : Prop := ∀ x, O.value 0 - O.value x ≤ Δ
def DualLocalized (G : ℝ) : Prop := ‖O.gradY 0 0‖ ≤ G

theorem initial_dual_distance {G : ℝ} (hG : O.DualLocalized G) : ‖O.dualMax 0‖ ≤ G / μ := by
  have h := (O.residual_distance 0 0).1
  simp only [zero_sub, norm_neg] at h
  apply (le_div_iff₀ O.μ_pos).mpr
  change ‖O.gradY 0 0‖ ≤ G at hG
  nlinarith

end NCObjective
end FreshGradientMinimax
