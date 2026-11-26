import FreshGradientMinimax.AcceleratedCap

/-! The actual intrinsic protected F_delta, with strong concavity and the
same genuine maximizer as the uncapped formula at the paper's threshold. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

def acceleratedProtected (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : ℝ :=
  acceleratedPrimal n k δ u - robinStep (n + 2) ^ 2 / 2 * ‖y‖ ^ 2 - acceleratedCap n k δ u y

def acceleratedProtectedGradientY (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) : Euclid (k * (n + 2)) :=
  -(robinStep (n + 2) ^ 2 • y) - acceleratedCapGradientY n k δ u y

theorem acceleratedProtected_hasFDerivAt_y (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    HasFDerivAt (acceleratedProtected n k δ u) (innerSL ℝ (acceleratedProtectedGradientY n k δ u y)) y := by
  have hn := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (robinStep (n + 2) ^ 2 / 2)
  have hd := ((hasFDerivAt_const (acceleratedPrimal n k δ u) y).sub hn).sub
    (acceleratedCap_hasFDerivAt_y n k hδ u y)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [acceleratedProtectedGradientY, innerSL_apply, inner_sub_left, inner_neg_left, real_inner_smul_left]
  ring

theorem acceleratedProtected_strongConcave (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (u : Euclid (k * 2 + 1)) :
    StrongConcaveGradient (acceleratedProtected n k δ u) (acceleratedProtectedGradientY n k δ u) (robinStep (n + 2) ^ 2) := by
  simpa only [acceleratedProtected, acceleratedProtectedGradientY, inner_zero_left, add_zero, zero_sub] using
    convex_penalty_strongConcave (acceleratedCap_convex_y n k hδ u)
      (acceleratedCap_hasFDerivAt_y n k hδ u) (robinStep (n + 2) ^ 2)
      (acceleratedPrimal n k δ u) (0 : Euclid (k * (n + 2)))

theorem acceleratedProtected_joint_contDiff (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ContDiff ℝ 1 (fun z : Euclid (k * 2 + 1) × Euclid (k * (n + 2)) => acceleratedProtected n k δ z.1 z.2) :=
  (((acceleratedPrimal_contDiff n k hδ).comp contDiff_fst).sub
    (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_snd))).sub (acceleratedCap_joint_contDiff n k hδ)

theorem acceleratedProtected_le_uncapped (n k : ℕ) (δ : ℝ)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    acceleratedProtected n k δ u y ≤ acceleratedUncapped n k δ u y :=
  sub_le_sub_left (acceleratedCap_ge_energy n k δ u y) _

theorem acceleratedProtected_core {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) {y : Euclid (k * (n + 2))} (hy : ‖y‖ ≤ acceleratedDualRadius n k) :
    acceleratedProtected n k δ u y = acceleratedUncapped n k δ u y := by
  unfold acceleratedProtected acceleratedUncapped
  rw [acceleratedCap_core hn hδ u hy]

theorem acceleratedProtected_at_maximizer {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k) (u : Euclid (k * 2 + 1)) :
    acceleratedProtected n k (acceleratedThreshold n k) u
        (acceleratedHuberMaximizer n k (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le) =
      acceleratedUncapped n k (acceleratedThreshold n k) u
        (acceleratedHuberMaximizer n k (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le) := by
  apply acceleratedProtected_core hn (acceleratedThreshold_pos n hk).le
  exact (acceleratedHuberMaximizer_in_core hn hk u).le.trans (by have := acceleratedDualRadius_pos n k; linarith)

theorem acceleratedProtected_maximizer {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k)
    (u : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    acceleratedProtected n k (acceleratedThreshold n k) u y ≤
      acceleratedProtected n k (acceleratedThreshold n k) u
        (acceleratedHuberMaximizer n k (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le) := by
  rw [acceleratedProtected_at_maximizer hn hk u]
  exact (acceleratedProtected_le_uncapped _ _ _ _ _).trans
    (acceleratedHuberMaximizer_max n k (acceleratedThreshold_pos n hk).le u y)

theorem robinMultiEnergy_zero_dual_bound {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) : robinMultiEnergy n k δ u 0 ≤ 756 * (k + 1 : ℕ) := by
  have h := (boundedEnergy_bounds hδ (by norm_num : (0 : ℝ) ≤ 1000)
    (robinBlockEdges n k (clipVector 2 u) 0)).2
  change robinMultiEnergy n k δ u 0 ≤ _ at h
  simp only [robinBlockEdges, map_zero, zero_add] at h
  have hA := robinPrimalMap_norm_sq_bound hn k (clipVector 2 u)
  have hclip := clip_two_norm_sq u
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at *
  nlinarith only [h, hA, hclip]

theorem acceleratedProtected_zero_dual_lower {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) : -1000 * (k + 1 : ℕ) ≤ acceleratedProtected n k δ u 0 := by
  rw [acceleratedProtected_core hn hδ u (by simpa only [norm_zero] using (acceleratedDualRadius_pos n k).le)]
  unfold acceleratedUncapped
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
  have hD := acceleratedPrimal_lower hn hδ u
  have hQ := robinMultiEnergy_zero_dual_bound hn hδ u
  nlinarith only [hD, hQ, Nat.cast_nonneg (α := ℝ) (k + 1)]

theorem acceleratedProtected_value_lower {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k) (u : Euclid (k * 2 + 1)) :
    -1000 * (k + 1 : ℕ) ≤ acceleratedProtected n k (acceleratedThreshold n k) u
      (acceleratedHuberMaximizer n k (acceleratedThreshold n k) u (acceleratedThreshold_pos n hk).le) :=
  (acceleratedProtected_zero_dual_lower hn (acceleratedThreshold_pos n hk).le u).trans
    (acceleratedProtected_maximizer hn hk u 0)

end FreshGradientMinimax
