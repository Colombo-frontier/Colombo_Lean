import FreshGradientMinimax.AffineBoundedEnergy
import FreshGradientMinimax.ClipVector

/-! Joint regularity and gradient estimates for clipped affine Huber sums. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

theorem boundedEnergy_contDiff {m : ℕ} {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) :
    ContDiff ℝ 1 (boundedEnergy (n := m) δ b) := by
  apply ContDiff.sum
  intro i _
  exact (boundedFlatEdge_contDiff hδ hb).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

theorem boundedSlope_difference {m : ℕ} {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (x y : Euclid m) :
    ‖boundedSlope δ b x - boundedSlope δ b y‖ ≤ ‖x - y‖ := by
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using (boundedSlope_lipschitz hδ hb).dist_le_mul x y

theorem bounded_pullback_difference {n m : ℕ} (A : Euclid n →L[ℝ] Euclid m)
    {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (x y : Euclid m) :
    ‖(A†) (boundedSlope δ b x) - (A†) (boundedSlope δ b y)‖ ≤ ‖A‖ * ‖x - y‖ := by
  rw [← map_sub]
  have h := (A†).le_opNorm (boundedSlope δ b x - boundedSlope δ b y)
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans (mul_le_mul_of_nonneg_left (boundedSlope_difference hδ hb x y) (norm_nonneg A))

theorem clipped_scalar_hasFDerivAt {n : ℕ} {f : Euclid n → ℝ} {R : ℝ} (hR : 0 < R)
    (u w : Euclid n) (hf : HasFDerivAt f (innerSL ℝ w) (clipVector R u)) :
    HasFDerivAt (fun v => f (clipVector R v)) (innerSL ℝ (weightedClipGradient R w u)) u := by
  have hc := ((clipVector_contDiff (n := n) R).differentiable (by norm_num) u).hasFDerivAt
  have hcomp := hf.comp u hc
  have hw := (innerSL ℝ w).hasFDerivAt.comp u hc
  have he := hw.unique (weightedClip_hasFDerivAt hR w u)
  exact hcomp.congr_fderiv he

theorem weightedClipGradient_two_changes {n : ℕ} {R W : ℝ} (hR : 0 < R) (hW : 0 ≤ W)
    (w v x y : Euclid n) (hv : ∀ i, |v i| ≤ W) :
    ‖weightedClipGradient R w x - weightedClipGradient R v y‖ ≤
      ‖w - v‖ + (W * (3 / (2 * R))) * ‖x - y‖ := by
  have h : ‖weightedClipGradient R w x - weightedClipGradient R v y‖ ≤
      ‖weightedClipGradient R w x - weightedClipGradient R v x‖ +
        ‖weightedClipGradient R v x - weightedClipGradient R v y‖ := by
    calc
      _ = ‖(weightedClipGradient R w x - weightedClipGradient R v x) +
          (weightedClipGradient R v x - weightedClipGradient R v y)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  exact h.trans (add_le_add (weightedClipGradient_sub_weights R w v x)
    (weightedClipGradient_sub_norm hR hW v hv x y))

end FreshGradientMinimax
