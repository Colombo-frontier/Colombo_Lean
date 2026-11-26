import FreshGradientMinimax.CoordinateScaling

/-! Scaling preserves the actual global maximizer, supremum and its true
gradient. Gap and localization estimates transfer with their exact factors. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {dx dy : ℕ} {L μ lam r : ℝ} (O : NCObjective dx dy L μ)
  (hlam : 0 < lam) (hr : 0 < r)

theorem coordinateScaledModel_dualMax (x : Euclid dx) :
    (coordinateScaledModel O hlam hr).dualMax x = r • O.dualMax (r⁻¹ • x) := by
  apply ((coordinateScaledModel O hlam hr).dualMax_unique x _ ?_).symm
  intro y
  change lam * O.f (r⁻¹ • x) (r⁻¹ • y) ≤ lam * O.f (r⁻¹ • x) (r⁻¹ • (r • O.dualMax (r⁻¹ • x)))
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  exact mul_le_mul_of_nonneg_left (O.le_dualMax _ _) hlam.le

theorem coordinateScaledModel_value (x : Euclid dx) :
    (coordinateScaledModel O hlam hr).value x = lam * O.value (r⁻¹ • x) := by
  rw [NCObjective.value_eq_max, coordinateScaledModel_dualMax]
  change lam * O.f (r⁻¹ • x) (r⁻¹ • (r • O.dualMax (r⁻¹ • x))) = _
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul, O.value_eq_max]

theorem coordinateScaledModel_primalGradient (x : Euclid dx) :
    (coordinateScaledModel O hlam hr).primalGradient x = (lam / r) • O.primalGradient (r⁻¹ • x) := by
  unfold NCObjective.primalGradient
  rw [coordinateScaledModel_dualMax]
  change (lam / r) • O.gradX (r⁻¹ • x) (r⁻¹ • (r • O.dualMax (r⁻¹ • x))) = _
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem coordinateScaledModel_true_gradient (x : Euclid dx) :
    gradient (coordinateScaledModel O hlam hr).value x = (lam / r) • gradient O.value (r⁻¹ • x) := by
  rw [NCObjective.true_primal_gradient, coordinateScaledModel_primalGradient, O.true_primal_gradient]

theorem coordinateScaledModel_gradient_norm (x : Euclid dx) :
    ‖(coordinateScaledModel O hlam hr).primalGradient x‖ = (lam / r) * ‖O.primalGradient (r⁻¹ • x)‖ := by
  rw [coordinateScaledModel_primalGradient, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hlam hr)]

theorem coordinateScaledModel_gap {Δ : ℝ} (hgap : O.PrimalGapAtMost Δ) :
    (coordinateScaledModel O hlam hr).PrimalGapAtMost (lam * Δ) := by
  intro x
  rw [coordinateScaledModel_value, coordinateScaledModel_value, smul_zero, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (hgap (r⁻¹ • x)) hlam.le

theorem coordinateScaledModel_localized {G : ℝ} (hG : O.DualLocalized G) :
    (coordinateScaledModel O hlam hr).DualLocalized ((lam / r) * G) := by
  change ‖(lam / r) • O.gradY (r⁻¹ • 0) (r⁻¹ • 0)‖ ≤ _
  rw [smul_zero, smul_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hlam hr)]
  exact mul_le_mul_of_nonneg_left hG (div_pos hlam hr).le

theorem coordinateScaledModel_gradient_lower (x : Euclid dx) {c : ℝ}
    (hc : c ≤ ‖O.primalGradient (r⁻¹ • x)‖) :
    (lam / r) * c ≤ ‖(coordinateScaledModel O hlam hr).primalGradient x‖ := by
  rw [coordinateScaledModel_gradient_norm]
  exact mul_le_mul_of_nonneg_left hc (div_pos hlam hr).le

end FreshGradientMinimax
