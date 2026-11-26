import FreshGradientMinimax.WeightedRootLinks

/-! The actual adjoint Jacobian and the weighted Hessian estimate used in C.2. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def weightedCoreLinks {n : ℕ} (w : Euclid (n + n)) (u : Euclid (n + 1)) : ℝ := ⟪w, coreLinks u⟫_ℝ

def coreLinksPullback {n : ℕ} (w : Euclid (n + n)) (u : Euclid (n + 1)) : Euclid (n + 1) :=
  ((fderiv ℝ (@coreLinks n) u)†) w

theorem weightedCoreLinks_hasFDerivAt {n : ℕ} (w : Euclid (n + n)) (u : Euclid (n + 1)) :
    HasFDerivAt (weightedCoreLinks w) (innerSL ℝ (coreLinksPullback w u)) u := by
  have hd := (innerSL ℝ w).hasFDerivAt.comp u
    ((coreLinks_contDiff (m := 1)).differentiable (by norm_num) u).hasFDerivAt
  apply hd.congr_fderiv
  ext v
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply, coreLinksPullback,
    ContinuousLinearMap.adjoint_inner_left]

theorem weightedCoreLinks_gradient {n : ℕ} (w : Euclid (n + n)) (u : Euclid (n + 1)) :
    gradient (weightedCoreLinks w) u = coreLinksPullback w u :=
  (hasGradientAt_iff_hasFDerivAt.mpr (weightedCoreLinks_hasFDerivAt w u)).gradient

theorem weightedCoreLinks_split {n : ℕ} (w : Euclid (n + n)) (u : Euclid (n + 1)) :
    weightedCoreLinks w u = weightedRootLinks (-1) (euclidLeft w) u +
      weightedRootLinks 1 (euclidRight w) u := by
  rw [weightedCoreLinks, euclid_inner_blocks]
  simp [weightedRootLinks, PiLp.inner_apply, RCLike.inner_apply', euclidLeft, euclidRight,
    coreLinks, adjacentVector_apply, mul_comm]

theorem coreLinksPullback_split {n : ℕ} (w : Euclid (n + n)) (u : Euclid (n + 1)) :
    coreLinksPullback w u = weightedRootGradient (-1) (euclidLeft w) u +
      weightedRootGradient 1 (euclidRight w) u := by
  have hd := (weightedRootLinks_hasFDerivAt (-1) (euclidLeft w) u).add
    (weightedRootLinks_hasFDerivAt 1 (euclidRight w) u)
  have hfun : weightedCoreLinks w = fun v => weightedRootLinks (-1) (euclidLeft w) v +
      weightedRootLinks 1 (euclidRight w) v := funext (weightedCoreLinks_split w)
  rw [← hfun, ← map_add] at hd
  have hg := (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient
  rwa [weightedCoreLinks_gradient] at hg

theorem coreLinksPullback_norm {n : ℕ} (w : Euclid (n + n)) (u : Euclid (n + 1)) :
    ‖coreLinksPullback w u‖ ≤ 57 * ‖w‖ := by
  have h := ((fderiv ℝ (@coreLinks n) u)†).le_opNorm w
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans (mul_le_mul_of_nonneg_right (coreLinks_fderiv_norm u) (norm_nonneg w))

theorem coreLinksPullback_sub_weights {n : ℕ} (w v : Euclid (n + n)) (u : Euclid (n + 1)) :
    coreLinksPullback w u - coreLinksPullback v u = coreLinksPullback (w - v) u := by
  simp only [coreLinksPullback, map_sub]

theorem coreLinksPullback_sub_weight_norm {n : ℕ} (w v : Euclid (n + n)) (u : Euclid (n + 1)) :
    ‖coreLinksPullback w u - coreLinksPullback v u‖ ≤ 57 * ‖w - v‖ := by
  rw [coreLinksPullback_sub_weights]
  exact coreLinksPullback_norm _ _

theorem coreLinksPullback_sub_norm {n : ℕ} {W : ℝ} (hW : 0 ≤ W)
    (w : Euclid (n + n)) (hw : ∀ i, |w i| ≤ W) (u v : Euclid (n + 1)) :
    ‖coreLinksPullback w u - coreLinksPullback w v‖ ≤ 8000 * W * ‖u - v‖ := by
  have h1 := weightedRootGradient_sub_norm (by norm_num : |(-1 : ℝ)| = 1) hW (euclidLeft w)
    (fun e => hw (e.castAdd n)) u v
  have h2 := weightedRootGradient_sub_norm (by norm_num : |(1 : ℝ)| = 1) hW (euclidRight w)
    (fun e => hw (e.natAdd n)) u v
  rw [coreLinksPullback_split, coreLinksPullback_split]
  have he : (weightedRootGradient (-1) (euclidLeft w) u + weightedRootGradient 1 (euclidRight w) u) -
      (weightedRootGradient (-1) (euclidLeft w) v + weightedRootGradient 1 (euclidRight w) v) =
      (weightedRootGradient (-1) (euclidLeft w) u - weightedRootGradient (-1) (euclidLeft w) v) +
      (weightedRootGradient 1 (euclidRight w) u - weightedRootGradient 1 (euclidRight w) v) := by abel
  rw [he]
  have h := norm_add_le
    (weightedRootGradient (-1) (euclidLeft w) u - weightedRootGradient (-1) (euclidLeft w) v)
    (weightedRootGradient 1 (euclidRight w) u - weightedRootGradient 1 (euclidRight w) v)
  linarith only [h, h1, h2]

theorem weightedCoreLinks_gradient_lipschitz {n : ℕ} {W : ℝ} (hW : 0 ≤ W)
    (w : Euclid (n + n)) (hw : ∀ i, |w i| ≤ W) :
    LipschitzWith ⟨8000 * W, by positivity⟩ (gradient (weightedCoreLinks w)) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro u v
  simpa only [weightedCoreLinks_gradient, NNReal.coe_mk] using coreLinksPullback_sub_norm hW w hw u v

theorem weightedCoreLinks_hessian_bound {n : ℕ} {W : ℝ} (hW : 0 ≤ W)
    (w : Euclid (n + n)) (hw : ∀ i, |w i| ≤ W) (u : Euclid (n + 1)) :
    ‖fderiv ℝ (gradient (weightedCoreLinks w)) u‖ ≤ 8000 * W :=
  norm_fderiv_le_of_lipschitz ℝ (weightedCoreLinks_gradient_lipschitz hW w hw)

end FreshGradientMinimax
