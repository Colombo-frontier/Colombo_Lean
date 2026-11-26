import FreshGradientMinimax.AcceleratedValuePerturbation
import FreshGradientMinimax.AcceleratedOrigin
import FreshGradientMinimax.AcceleratedCapPrimal

/-! The actual supremum of the protected objective equals the uncapped
value at the original threshold. This transfers the true gradient estimate. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

def acceleratedProtectedValue (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) : ℝ :=
  sSup (Set.range (acceleratedProtected n k δ u))

theorem acceleratedProtectedValue_eq_max {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k)
    (u : Euclid (k * 2 + 1)) :
    acceleratedProtectedValue n k (acceleratedThreshold n k) u =
      acceleratedProtected n k (acceleratedThreshold n k) u
        (acceleratedHuberMaximizer n k (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le) := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨_, rfl⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact acceleratedProtected_maximizer hn hk u y

theorem acceleratedProtectedValue_eq_value {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k) :
    acceleratedProtectedValue n k (acceleratedThreshold n k) = acceleratedValue n k (acceleratedThreshold n k) := by
  funext u
  rw [acceleratedProtectedValue_eq_max hn hk, acceleratedProtected_at_maximizer hn hk,
    acceleratedValue_eq_max hn (acceleratedThreshold_pos n hk).le]

theorem acceleratedProtectedValue_hasFDerivAt {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k)
    (u : Euclid (k * 2 + 1)) :
    HasFDerivAt (acceleratedProtectedValue n k (acceleratedThreshold n k))
      (innerSL ℝ (acceleratedUncappedGradientU n k (acceleratedThreshold n k) u
        (acceleratedHuberMaximizer n k (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le))) u := by
  rw [acceleratedProtectedValue_eq_value hn hk]
  exact acceleratedValue_hasFDerivAt hn (acceleratedThreshold_pos n hk).le u

theorem acceleratedProtectedValue_gradient_comparison {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k)
    (u : Euclid (k * 2 + 1)) :
    ‖gradient (acceleratedProtectedValue n k (acceleratedThreshold n k)) u - gradient acceleratedIdealValue u‖ ≤
      primalRidgeConstant / 100 := by
  rw [acceleratedProtectedValue_eq_value hn hk]
  exact acceleratedValue_gradient_comparison hn hk u

theorem acceleratedProtectedValue_lower {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k)
    (u : Euclid (k * 2 + 1)) :
    -1000 * (k + 1 : ℕ) ≤ acceleratedProtectedValue n k (acceleratedThreshold n k) u := by
  rw [acceleratedProtectedValue_eq_max hn hk]
  exact acceleratedProtected_value_lower hn hk u

theorem acceleratedProtectedValue_origin {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    acceleratedProtectedValue n k δ 0 = -coreTheta 0 := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨0, acceleratedProtected_origin hn hδ⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact acceleratedProtected_origin_max hn hδ y

theorem acceleratedProtectedValue_gradient_norm {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k)
    (u : Euclid (k * 2 + 1)) :
    ‖gradient (acceleratedProtectedValue n k (acceleratedThreshold n k)) u‖ ≤
      15000 * Real.sqrt (k + 1 : ℕ) := by
  rw [acceleratedProtectedValue_eq_value hn hk]
  exact acceleratedValue_gradient_norm hn (acceleratedThreshold_pos n hk).le u

def acceleratedProtectedGradientU (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1))
    (y : Euclid (k * (n + 2))) : Euclid (k * 2 + 1) :=
  acceleratedPrimalGradient n k δ u - acceleratedCapGradientU n k δ u y

theorem acceleratedProtected_hasFDerivAt_u (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    HasFDerivAt (fun v => acceleratedProtected n k δ v y)
      (innerSL ℝ (acceleratedProtectedGradientU n k δ u y)) u := by
  have h := ((acceleratedPrimal_hasFDerivAt n k hδ u).sub
    (hasFDerivAt_const (robinStep (n + 2) ^ 2 / 2 * ‖y‖ ^ 2) u)).sub
    (acceleratedCap_hasFDerivAt_u n k hδ u y)
  apply h.congr_fderiv
  ext v
  simp [acceleratedProtectedGradientU, innerSL_apply, inner_sub_left]

theorem acceleratedProtectedGradientU_norm {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖acceleratedProtectedGradientU n k δ u y‖ ≤ 15000 * Real.sqrt (k + 1 : ℕ) := by
  have h := norm_sub_le (acceleratedPrimalGradient n k δ u) (acceleratedCapGradientU n k δ u y)
  change ‖acceleratedProtectedGradientU n k δ u y‖ ≤ _ at h
  linarith only [h, acceleratedPrimalGradient_norm hn hδ u, acceleratedCapGradientU_norm hn hδ u y]

theorem acceleratedProtected_gradient_u (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    gradient (fun v => acceleratedProtected n k δ v y) u = acceleratedProtectedGradientU n k δ u y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (acceleratedProtected_hasFDerivAt_u n k hδ u y)).gradient

theorem acceleratedProtected_hasFDerivAt_joint (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (z : Joint (k * 2 + 1) (k * (n + 2))) :
    HasFDerivAt (fun w : Joint (k * 2 + 1) (k * (n + 2)) => acceleratedProtected n k δ w.1 w.2)
      ((innerSL ℝ (acceleratedProtectedGradientU n k δ z.1 z.2)).coprod
        (innerSL ℝ (acceleratedProtectedGradientY n k δ z.1 z.2))) z := by
  have h := joint_hasFDerivAt_gradient
    ((acceleratedProtected_joint_contDiff n k hδ).differentiable (by norm_num) z)
  have hy := (hasGradientAt_iff_hasFDerivAt.mpr (acceleratedProtected_hasFDerivAt_y n k hδ z.1 z.2)).gradient
  simpa only [acceleratedProtected_gradient_u n k hδ, hy] using h

end FreshGradientMinimax
