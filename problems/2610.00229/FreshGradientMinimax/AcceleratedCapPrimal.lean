import FreshGradientMinimax.AcceleratedCap

/-! The cap's actual primal partial gradient retains the original uniform
bound, globally across both interfaces of the smooth maximum. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

def acceleratedCapGradientU (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : Euclid (k * 2 + 1) :=
  (1 - acceleratedCapWeight n k δ u y) • robinMultiGradientU n k δ u y

theorem acceleratedCapWeight_bounds (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    0 ≤ acceleratedCapWeight n k δ u y ∧ acceleratedCapWeight n k δ u y ≤ 1 :=
  smoothRampSlope_bounds (sq_pos_of_pos (acceleratedDualRadius_pos n k)) _

theorem acceleratedCap_hasFDerivAt_u (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    HasFDerivAt (fun v => acceleratedCap n k δ v y) (innerSL ℝ (acceleratedCapGradientU n k δ u y)) u := by
  have h := smoothMaximum_comp_hasFDerivAt (sq_pos_of_pos (acceleratedDualRadius_pos n k))
    (robinMultiEnergy_hasFDerivAt_u n k hδ u y) (hasFDerivAt_const (acceleratedWall n k y) u)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [acceleratedCapGradientU, acceleratedCapWeight, innerSL_apply, real_inner_smul_left]

theorem acceleratedCap_gradient_u (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    gradient (fun v => acceleratedCap n k δ v y) u = acceleratedCapGradientU n k δ u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (acceleratedCap_hasFDerivAt_u n k hδ u y)).gradient

theorem acceleratedCapGradientU_norm {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖acceleratedCapGradientU n k δ u y‖ ≤ 14000 * Real.sqrt (k + 1 : ℕ) := by
  have hw := acceleratedCapWeight_bounds n k δ u y
  unfold acceleratedCapGradientU
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - acceleratedCapWeight n k δ u y)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans (robinMultiGradientU_norm hn hδ u y)

end FreshGradientMinimax
