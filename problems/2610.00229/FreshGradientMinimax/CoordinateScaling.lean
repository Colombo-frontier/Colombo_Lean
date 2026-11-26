import FreshGradientMinimax.Objective

/-! Actual simultaneous scaling of both query variables and the function
value, with its exact derivatives, smoothness and strong concavity. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {dx dy : ℕ} {L μ : ℝ} (O : NCObjective dx dy L μ)

def coordinateScaledFunction (lam r : ℝ) (x : Euclid dx) (y : Euclid dy) : ℝ :=
  lam * O.f (r⁻¹ • x) (r⁻¹ • y)

def coordinateScaledGradX (lam r : ℝ) (x : Euclid dx) (y : Euclid dy) : Euclid dx :=
  (lam / r) • O.gradX (r⁻¹ • x) (r⁻¹ • y)

def coordinateScaledGradY (lam r : ℝ) (x : Euclid dx) (y : Euclid dy) : Euclid dy :=
  (lam / r) • O.gradY (r⁻¹ • x) (r⁻¹ • y)

theorem coordinateScaledFunction_hasFDerivAt (lam r : ℝ) (z : Joint dx dy) :
    HasFDerivAt (fun w : Joint dx dy => coordinateScaledFunction O lam r w.1 w.2)
      ((innerSL ℝ (coordinateScaledGradX O lam r z.1 z.2)).coprod
        (innerSL ℝ (coordinateScaledGradY O lam r z.1 z.2))) z := by
  have h := ((O.derivative (r⁻¹ • z)).comp z ((hasFDerivAt_id z).const_smul r⁻¹)).const_mul lam
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.coprod_apply, innerSL_apply, Prod.smul_fst, Prod.smul_snd,
    coordinateScaledGradX, coordinateScaledGradY, real_inner_smul_left, real_inner_smul_right,
    smul_eq_mul, div_eq_mul_inv]
  ring

theorem coordinateScaledGrad_joint_smooth (lam r : ℝ) (x z : Euclid dx) (y w : Euclid dy) :
    ‖coordinateScaledGradX O lam r x y - coordinateScaledGradX O lam r z w‖ ^ 2 +
      ‖coordinateScaledGradY O lam r x y - coordinateScaledGradY O lam r z w‖ ^ 2 ≤
      (lam * L / r ^ 2) ^ 2 * (‖x - z‖ ^ 2 + ‖y - w‖ ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (O.joint_smooth (r⁻¹ • x) (r⁻¹ • y) (r⁻¹ • z) (r⁻¹ • w))
    (sq_nonneg (lam / r))
  simp only [← smul_sub, norm_smul_sq] at h
  simp only [coordinateScaledGradX, coordinateScaledGradY, ← smul_sub, norm_smul_sq]
  convert h using 1 <;> simp only [div_eq_mul_inv, inv_pow] <;> ring

theorem coordinateScaledFunction_strongConcave {lam : ℝ} (hlam : 0 ≤ lam) (r : ℝ) (x : Euclid dx) :
    StrongConcaveGradient (coordinateScaledFunction O lam r x) (coordinateScaledGradY O lam r x)
      (lam * μ / r ^ 2) := by
  intro y z
  have h := mul_le_mul_of_nonneg_left (O.dual_strong (r⁻¹ • x) (r⁻¹ • y) (r⁻¹ • z)) hlam
  simp only [← smul_sub, real_inner_smul_right, norm_smul_sq] at h
  simp only [coordinateScaledFunction, coordinateScaledGradY, real_inner_smul_left]
  convert h using 1
  simp only [div_eq_mul_inv, inv_pow]
  ring

def coordinateScaledModel {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) :
    NCObjective dx dy (lam * L / r ^ 2) (lam * μ / r ^ 2) where
  μ_pos := div_pos (mul_pos hlam O.μ_pos) (sq_pos_of_pos hr)
  μ_le_L := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left O.μ_le_L hlam.le) (sq_nonneg r)
  f := coordinateScaledFunction O lam r
  gradX := coordinateScaledGradX O lam r
  gradY := coordinateScaledGradY O lam r
  derivative := coordinateScaledFunction_hasFDerivAt O lam r
  joint_smooth := fun x y z w => coordinateScaledGrad_joint_smooth O lam r x z y w
  dual_strong := coordinateScaledFunction_strongConcave O hlam.le r

namespace NCObjective

def weakenConstants {L' μ' : ℝ} (hL : L ≤ L') (hμ : 0 < μ') (hμ' : μ' ≤ μ) : NCObjective dx dy L' μ' where
  μ_pos := hμ
  μ_le_L := hμ'.trans (O.μ_le_L.trans hL)
  f := O.f
  gradX := O.gradX
  gradY := O.gradY
  derivative := O.derivative
  joint_smooth := by
    intro x y z w
    exact (O.joint_smooth x y z w).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ O.L_pos.le hL 2) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  dual_strong := by
    intro x y z
    have h := O.dual_strong x y z
    have hm := mul_le_mul_of_nonneg_right hμ' (sq_nonneg ‖z - y‖)
    change O.f x z ≤ O.f x y + _ - _
    linarith only [h, hm]

theorem weakenConstants_value {L' μ' : ℝ} (hL : L ≤ L') (hμ : 0 < μ') (hμ' : μ' ≤ μ) :
    (O.weakenConstants hL hμ hμ').value = O.value := rfl

theorem weakenConstants_primalGradient {L' μ' : ℝ} (hL : L ≤ L') (hμ : 0 < μ') (hμ' : μ' ≤ μ)
    (x : Euclid dx) : (O.weakenConstants hL hμ hμ').primalGradient x = O.primalGradient x := by
  rw [← NCObjective.true_primal_gradient, weakenConstants_value, NCObjective.true_primal_gradient]

end NCObjective
end FreshGradientMinimax
