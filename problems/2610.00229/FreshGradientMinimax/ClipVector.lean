import FreshGradientMinimax.WeightedCoreLinks
import FreshGradientMinimax.SmoothClip

/-! Coordinate clipping on Euclidean space, including weighted derivatives. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace

def clipVector {n : ℕ} (R : ℝ) (x : Euclid n) : Euclid n :=
  (WithLp.equiv 2 _).symm (fun i => smoothClip R (x i))

@[simp]
theorem clipVector_apply {n : ℕ} (R : ℝ) (x : Euclid n) (i : Fin n) :
    clipVector R x i = smoothClip R (x i) := rfl

theorem euclid_norm_le_of_coordinate_comparison {n : ℕ} (x y : Euclid n) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, |x i| ≤ C * |y i|) : ‖x‖ ≤ C * ‖y‖ := by
  have hsq : ‖x‖ ^ 2 ≤ C ^ 2 * ‖y‖ ^ 2 := by
    rw [euclid_norm_sq, euclid_norm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h i) 2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  nlinarith only [hsq]

theorem clipVector_sub_norm {n : ℕ} {R : ℝ} (hR : 0 < R) (x y : Euclid n) :
    ‖clipVector R x - clipVector R y‖ ≤ ‖x - y‖ := by
  simpa only [one_mul] using euclid_norm_le_of_coordinate_comparison
    (clipVector R x - clipVector R y) (x - y) (by norm_num : (0 : ℝ) ≤ 1)
    (fun i => by simpa only [one_mul] using smoothClip_lipschitz hR (x i) (y i))

theorem clipVector_norm_le {n : ℕ} {R : ℝ} (hR : 0 < R) (x : Euclid n) :
    ‖clipVector R x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using euclid_norm_le_of_coordinate_comparison
    (clipVector R x) x (by norm_num : (0 : ℝ) ≤ 1)
    (fun i => by simpa only [one_mul] using smoothClip_le_abs hR (x i))

theorem clipVector_norm_bound {n : ℕ} {R : ℝ} (hR : 0 < R) (x : Euclid n) :
    ‖clipVector R x‖ ≤ (3 * R / 2) * Real.sqrt (n : ℝ) :=
  euclid_norm_le_of_coordinate_bound _ (by positivity) (fun i => smoothClip_bound hR (x i))

theorem clipVector_identity {n : ℕ} {R : ℝ} (hR : 0 < R) (x : Euclid n)
    (hx : ∀ i, |x i| ≤ R) : clipVector R x = x := by
  ext i
  exact smoothClip_identity hR (hx i)

theorem clipVector_contDiff {n : ℕ} (R : ℝ) : ContDiff ℝ 2 (@clipVector n R) := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact (smoothClip_contDiff R).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

theorem smoothClipSlope_sub_le {R : ℝ} (hR : 0 < R) (x y : ℝ) :
    |smoothClipSlope R x - smoothClipSlope R y| ≤ (3 / (2 * R)) * |x - y| :=
  scalar_sub_le_of_derivative_bound (smoothClipSlope_derivative hR) (smoothClipCurve_bound hR) x y

def weightedClip {n : ℕ} (R : ℝ) (w x : Euclid n) : ℝ := ⟪w, clipVector R x⟫_ℝ

def weightedClipGradient {n : ℕ} (R : ℝ) (w x : Euclid n) : Euclid n :=
  coordinateMultiplier (fun i => smoothClipSlope R (x i)) w

theorem weightedClip_hasFDerivAt {n : ℕ} {R : ℝ} (hR : 0 < R) (w x : Euclid n) :
    HasFDerivAt (weightedClip R w) (innerSL ℝ (weightedClipGradient R w x)) x := by
  have hd : HasFDerivAt (fun y : Euclid n => ∑ i, w i * smoothClip R (y i))
      (∑ i, (w i * smoothClipSlope R (x i)) • EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    apply HasFDerivAt.sum
    intro i _
    convert ((smoothClip_derivative hR (x i)).comp_hasFDerivAt x
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt).const_mul (w i) using 1
    rw [smul_smul]
  have hf : weightedClip R w = fun y : Euclid n => ∑ i, w i * smoothClip R (y i) := by
    funext y
    simp [weightedClip, PiLp.inner_apply, RCLike.inner_apply', mul_comm]
  rw [← hf] at hd
  apply hd.congr_fderiv
  ext v
  simp [weightedClipGradient, innerSL_apply, PiLp.inner_apply, RCLike.inner_apply',
    EuclideanSpace.proj, mul_comm, mul_left_comm, mul_assoc]

theorem weightedClipGradient_norm {n : ℕ} (R : ℝ) (w x : Euclid n) :
    ‖weightedClipGradient R w x‖ ≤ ‖w‖ := by
  apply coordinateMultiplier_norm_le
  intro i
  rw [abs_of_nonneg (smoothClipSlope_bounds R (x i)).1]
  exact (smoothClipSlope_bounds R (x i)).2

theorem weightedClipGradient_sub_weights {n : ℕ} (R : ℝ) (w v x : Euclid n) :
    ‖weightedClipGradient R w x - weightedClipGradient R v x‖ ≤ ‖w - v‖ := by
  rw [weightedClipGradient, weightedClipGradient, ← map_sub]
  exact weightedClipGradient_norm R (w - v) x

theorem weightedClipGradient_sub_norm {n : ℕ} {R W : ℝ} (hR : 0 < R) (hW : 0 ≤ W)
    (w : Euclid n) (hw : ∀ i, |w i| ≤ W) (x y : Euclid n) :
    ‖weightedClipGradient R w x - weightedClipGradient R w y‖ ≤ (W * (3 / (2 * R))) * ‖x - y‖ := by
  apply euclid_norm_le_of_coordinate_comparison _ _ (by positivity)
  intro i
  change |smoothClipSlope R (x i) * w i - smoothClipSlope R (y i) * w i| ≤
    (W * (3 / (2 * R))) * |x i - y i|
  rw [← sub_mul, abs_mul]
  have h := mul_le_mul (smoothClipSlope_sub_le hR (x i) (y i)) (hw i)
    (abs_nonneg _) (by positivity : 0 ≤ (3 / (2 * R)) * |x i - y i|)
  convert h using 1
  ring

end FreshGradientMinimax
