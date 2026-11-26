import FreshGradientMinimax.Minimax
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-! An explicit globally admissible objective, with its actual value,
gradient and localization. This supplies genuine lower-bound witnesses
without postulating their analytic properties. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def quadraticWitness (dx dy : ℕ) (L μ : ℝ) (hμ : 0 < μ) (hμL : μ ≤ L)
    (c : Euclid dx) : NCObjective dx dy L μ where
  μ_pos := hμ
  μ_le_L := hμL
  f x y := L / 2 * ‖x - c‖ ^ 2 - μ / 2 * ‖y‖ ^ 2
  gradX x _ := L • (x - c)
  gradY _ y := (-μ) • y
  derivative z := by
    have hx := (hasStrictFDerivAt_norm_sq (z.1 - c)).hasFDerivAt.comp z
      (hasFDerivAt_fst.sub_const c)
    have hy := (hasStrictFDerivAt_norm_sq z.2).hasFDerivAt.comp z hasFDerivAt_snd
    apply ((hx.const_mul (L / 2)).sub (hy.const_mul (μ / 2))).congr_fderiv
    apply ContinuousLinearMap.ext
    intro w
    simp [innerSL_apply, real_inner_smul_left]
    ring
  joint_smooth x y x' y' := by
    simp only [← smul_sub, sub_sub_sub_cancel_right, norm_smul_sq, neg_sq]
    have hL : 0 < L := hμ.trans_le hμL
    have hm : μ ^ 2 ≤ L ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg ‖y - y'‖)]
  dual_strong x := by
    intro y z
    have hn : ‖z‖ ^ 2 = ‖y‖ ^ 2 + 2 * ⟪y, z - y⟫_ℝ + ‖z - y‖ ^ 2 := by
      have he : y + (z - y) = z := by abel
      simpa only [he] using norm_add_sq_real y (z - y)
    simp only [real_inner_smul_left]
    nlinarith [congrArg (fun t : ℝ => μ * t) hn]

variable {dx dy : ℕ} {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (c : Euclid dx)

theorem quadraticWitness_dualMax (x : Euclid dx) :
    (quadraticWitness dx dy L μ hμ hμL c).dualMax x = 0 := by
  apply Eq.symm
  apply NCObjective.dualMax_unique
  intro y
  change L / 2 * ‖x - c‖ ^ 2 - μ / 2 * ‖y‖ ^ 2 ≤ L / 2 * ‖x - c‖ ^ 2 - μ / 2 * ‖(0 : Euclid dy)‖ ^ 2
  simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero]
  have h : 0 ≤ μ / 2 * ‖y‖ ^ 2 := by positivity
  linarith

theorem quadraticWitness_value (x : Euclid dx) :
    (quadraticWitness dx dy L μ hμ hμL c).value x = L / 2 * ‖x - c‖ ^ 2 := by
  rw [NCObjective.value_eq_max, quadraticWitness_dualMax]
  simp only [quadraticWitness, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero]

theorem quadraticWitness_gradient (x : Euclid dx) :
    gradient (quadraticWitness dx dy L μ hμ hμL c).value x = L • (x - c) := by
  rw [NCObjective.true_primal_gradient]
  rfl

theorem quadraticWitness_localized {G : ℝ} (hG : 0 ≤ G) :
    (quadraticWitness dx dy L μ hμ hμL c).DualLocalized G := by
  simpa only [NCObjective.DualLocalized, quadraticWitness, smul_zero, norm_zero] using hG

theorem quadraticWitness_gap :
    (quadraticWitness dx dy L μ hμ hμL c).PrimalGapAtMost (L / 2 * ‖c‖ ^ 2) := by
  intro x
  rw [quadraticWitness_value, quadraticWitness_value]
  simp only [zero_sub, norm_neg]
  have hL : 0 < L := hμ.trans_le hμL
  have hn : 0 ≤ L / 2 * ‖x - c‖ ^ 2 := by positivity
  linarith

theorem quadraticWitness_success_disjoint (d : Euclid dx) {ε : ℝ}
    (hsep : 2 * ε < L * ‖c - d‖) :
    Disjoint ((quadraticWitness dx dy L μ hμ hμL c).successSet ε)
      ((quadraticWitness dx dy L μ hμ hμL d).successSet ε) := by
  apply Set.disjoint_left.mpr
  intro x hx hd
  have hL : 0 < L := hμ.trans_le hμL
  change ‖gradient (quadraticWitness dx dy L μ hμ hμL c).value x‖ ≤ ε at hx
  change ‖gradient (quadraticWitness dx dy L μ hμ hμL d).value x‖ ≤ ε at hd
  rw [quadraticWitness_gradient, norm_smul, Real.norm_eq_abs, abs_of_pos hL] at hx hd
  have hn : ‖c - d‖ ≤ ‖x - c‖ + ‖x - d‖ := by
    calc
      _ = ‖(x - d) - (x - c)‖ := by congr 1; abel
      _ ≤ ‖x - d‖ + ‖x - c‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  nlinarith [mul_le_mul_of_nonneg_left hn hL.le]

end FreshGradientMinimax
