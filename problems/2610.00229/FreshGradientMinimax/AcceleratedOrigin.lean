import FreshGradientMinimax.AcceleratedProtected

/-! The exact origin value and actual zero dual maximizer of the protected
multi-chain formula, for every nonnegative flattening threshold. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

theorem clip_two_zero (m : ℕ) : clipVector 2 (0 : Euclid m) = 0 :=
  clipVector_identity (by norm_num) _ (by intro i; norm_num)

theorem acceleratedNonlinear_zero (k : ℕ) : acceleratedNonlinear (0 : Euclid (k * 2 + 1)) = -coreTheta 0 := by
  have h := (coreLinks_flat (by norm_num : |(0 : ℝ)| ≤ 1 / 2) 0).2.2
  simp [acceleratedNonlinear, h]

theorem acceleratedPrimal_origin (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    acceleratedPrimal n k δ 0 = -coreTheta 0 := by
  have hf := flatEdge_flat hδ (by simpa using hδ : |(0 : ℝ)| ≤ δ)
  rw [acceleratedPrimal, clip_two_zero]
  simp [acceleratedNonlinear_zero, hf]

theorem robinMultiEnergy_origin (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : robinMultiEnergy n k δ 0 0 = 0 := by
  have hf := boundedFlatEdge_flat hδ (by norm_num : (0 : ℝ) ≤ 1000) (by simpa using hδ : |(0 : ℝ)| ≤ δ)
  simp [robinMultiEnergy, clip_two_zero, robinBlockEdges, boundedEnergy, hf]

theorem robinMultiGradientY_origin (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : robinMultiGradientY n k δ 0 0 = 0 := by
  have hs : boundedSlope δ 1000 (0 : Euclid (k * (n + 3))) = 0 := by
    ext e
    exact boundedFlatSlope_flat hδ (by norm_num) (by simpa using hδ)
  simp [robinMultiGradientY, robinMultiSlope, clip_two_zero, robinBlockEdges, hs]

theorem acceleratedProtectedGradientY_origin (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    acceleratedProtectedGradientY n k δ 0 0 = 0 := by
  simp [acceleratedProtectedGradientY, acceleratedCapGradientY, robinMultiGradientY_origin n k hδ]

theorem acceleratedProtected_origin {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    acceleratedProtected n k δ 0 0 = -coreTheta 0 := by
  rw [acceleratedProtected_core hn hδ 0 (by simpa only [norm_zero] using (acceleratedDualRadius_pos n k).le)]
  simp [acceleratedUncapped, acceleratedPrimal_origin n k hδ, robinMultiEnergy_origin n k hδ]

theorem acceleratedProtected_origin_max {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (y : Euclid (k * (n + 2))) : acceleratedProtected n k δ 0 y ≤ -coreTheta 0 := by
  have h := acceleratedProtected_strongConcave n k hδ 0 0 y
  rw [acceleratedProtectedGradientY_origin n k hδ, inner_zero_left, add_zero, acceleratedProtected_origin hn hδ] at h
  exact h.trans (sub_le_self _ (by positivity))

theorem acceleratedProtected_maximizer_origin {n k : ℕ} (hn : 10 ≤ n + 2) (hk : 0 < k) :
    acceleratedHuberMaximizer n k (acceleratedThreshold n k) 0 (acceleratedThreshold_pos n hk).le = 0 := by
  apply strong_concave_maximum_unique (sq_pos_of_pos (robinStep_pos (show 0 < n + 2 by omega)))
    (acceleratedProtected_strongConcave n k (acceleratedThreshold_pos n hk).le 0)
    (acceleratedProtected_hasFDerivAt_y n k (acceleratedThreshold_pos n hk).le 0)
    _ 0 (acceleratedProtected_maximizer hn hk 0)
  intro y
  rw [acceleratedProtected_origin hn (acceleratedThreshold_pos n hk).le]
  exact acceleratedProtected_origin_max hn (acceleratedThreshold_pos n hk).le y

end FreshGradientMinimax
