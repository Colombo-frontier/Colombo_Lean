import FreshGradientMinimax.RobinMultiEnergy

/-! The original four uniform partial-gradient bounds for Q_delta. The
argument uses genuine C1 derivatives and includes the Huber interfaces. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem bounded_pullback_linear_increment {a p m : ℕ}
    (A : Euclid a →L[ℝ] Euclid m) (B : Euclid p →L[ℝ] Euclid m)
    {δ b C D : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hC : 0 ≤ C) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ D)
    (x y : Euclid m) (z : Euclid p) (he : x - y = B z) :
    ‖(A†) (boundedSlope δ b x) - (A†) (boundedSlope δ b y)‖ ≤ C * D * ‖z‖ := by
  have h := bounded_pullback_difference A hδ hb x y
  rw [he] at h
  have h1 := mul_le_mul_of_nonneg_left (B.le_opNorm z) (norm_nonneg A)
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul hA hB (norm_nonneg B) hC) (norm_nonneg z)
  exact h.trans (h1.trans (by simpa only [mul_assoc] using h2))

theorem robinBlockEdges_difference_u {n k : ℕ} (u v : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    robinBlockEdges n k u y - robinBlockEdges n k v y = robinPrimalMap n k (u - v) := by
  unfold robinBlockEdges
  rw [map_sub]
  abel

theorem robinBlockEdges_difference_y {n k : ℕ} (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) :
    robinBlockEdges n k u y - robinBlockEdges n k u z = robinDualMap n k (y - z) := by
  unfold robinBlockEdges
  rw [map_sub]
  abel

theorem robinMultiPullback_difference_u {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖robinMultiPullback n k δ u y - robinMultiPullback n k δ v y‖ ≤ 100 * ‖u - v‖ := by
  have hA : ‖robinPrimalMap n k‖ ≤ 10 := (robinPrimalMap_opNorm_bound hn k).trans (by norm_num)
  have h := bounded_pullback_linear_increment (robinPrimalMap n k) (robinPrimalMap n k)
    hδ (by norm_num : (0 : ℝ) ≤ 1000) (by norm_num : (0 : ℝ) ≤ 10) hA hA
    _ _ _ (robinBlockEdges_difference_u (clipVector 2 u) (clipVector 2 v) y)
  change ‖robinMultiPullback n k δ u y - robinMultiPullback n k δ v y‖ ≤ _ at h
  exact h.trans (by
    have hc := mul_le_mul_of_nonneg_left (clipVector_sub_norm (by norm_num : (0 : ℝ) < 2) u v)
      (by norm_num : (0 : ℝ) ≤ 100)
    norm_num only [show (10 : ℝ) * 10 = 100 by norm_num] at *
    exact hc)

theorem robinMultiGradientU_difference_u {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖robinMultiGradientU n k δ u y - robinMultiGradientU n k δ v y‖ ≤ 10 ^ 4 * ‖u - v‖ := by
  have h := weightedClipGradient_two_changes (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) ≤ (28 / 3) * 1000)
    (robinMultiPullback n k δ u y) (robinMultiPullback n k δ v y) u v
    (robinMultiPullback_coordinate hn hδ v y)
  change ‖robinMultiGradientU n k δ u y - robinMultiGradientU n k δ v y‖ ≤ _ at h
  nlinarith only [h, robinMultiPullback_difference_u hn hδ u v y, norm_nonneg (u - v)]

theorem robinMultiPullback_difference_y {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) :
    ‖robinMultiPullback n k δ u y - robinMultiPullback n k δ u z‖ ≤ 20 * ‖y - z‖ := by
  have hA : ‖robinPrimalMap n k‖ ≤ 10 := (robinPrimalMap_opNorm_bound hn k).trans (by norm_num)
  simpa only [robinMultiPullback, robinMultiSlope, show (10 : ℝ) * 2 = 20 by norm_num] using
    bounded_pullback_linear_increment (robinPrimalMap n k) (robinDualMap n k)
    (b := 1000) (C := 10) hδ (by norm_num) (by norm_num) hA (robinDualMap_opNorm n k)
    _ _ _ (robinBlockEdges_difference_y (clipVector 2 u) y z)

theorem robinMultiGradientU_difference_y {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) :
    ‖robinMultiGradientU n k δ u y - robinMultiGradientU n k δ u z‖ ≤ 21 * ‖y - z‖ := by
  have h := weightedClipGradient_sub_weights 2 (robinMultiPullback n k δ u y) (robinMultiPullback n k δ u z) u
  change ‖robinMultiGradientU n k δ u y - robinMultiGradientU n k δ u z‖ ≤ _ at h
  nlinarith only [h, robinMultiPullback_difference_y hn hδ u y z, norm_nonneg (y - z)]

theorem robinMultiGradientY_difference_u {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u v : Euclid (k * 2 + 1)) (y : Euclid (k * (n + 2))) :
    ‖robinMultiGradientY n k δ u y - robinMultiGradientY n k δ v y‖ ≤ 21 * ‖u - v‖ := by
  have hA : ‖robinPrimalMap n k‖ ≤ 10 := (robinPrimalMap_opNorm_bound hn k).trans (by norm_num)
  have h := bounded_pullback_linear_increment (robinDualMap n k) (robinPrimalMap n k)
    hδ (by norm_num : (0 : ℝ) ≤ 1000) (by norm_num) (robinDualMap_opNorm n k) hA
    _ _ _ (robinBlockEdges_difference_u (clipVector 2 u) (clipVector 2 v) y)
  change ‖robinMultiGradientY n k δ u y - robinMultiGradientY n k δ v y‖ ≤ _ at h
  have hc := mul_le_mul_of_nonneg_left (clipVector_sub_norm (by norm_num : (0 : ℝ) < 2) u v)
    (by norm_num : (0 : ℝ) ≤ 20)
  nlinarith only [h, hc, norm_nonneg (u - v)]

theorem robinMultiGradientY_difference_y (n k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) (y z : Euclid (k * (n + 2))) :
    ‖robinMultiGradientY n k δ u y - robinMultiGradientY n k δ u z‖ ≤ 5 * ‖y - z‖ := by
  have h := bounded_pullback_linear_increment (robinDualMap n k) (robinDualMap n k)
    hδ (by norm_num : (0 : ℝ) ≤ 1000) (by norm_num) (robinDualMap_opNorm n k) (robinDualMap_opNorm n k)
    _ _ _ (robinBlockEdges_difference_y (clipVector 2 u) y z)
  change ‖robinMultiGradientY n k δ u y - robinMultiGradientY n k δ u z‖ ≤ _ at h
  nlinarith only [h, norm_nonneg (y - z)]

end FreshGradientMinimax
