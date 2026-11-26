import FreshGradientMinimax.CoreLinksVector

/-! Actual gradients of weighted adjacent links, with a Hessian bound in
the maximum coordinate of the weights rather than their dimension. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace

def weightedRootLinks {n : ℕ} (s : ℝ) (w : Euclid n) (u : Euclid (n + 1)) : ℝ :=
  ∑ e : Fin n, w e * rootLink s (u e.castSucc) (u e.succ)

def weightedRootGradient {n : ℕ} (s : ℝ) (w : Euclid n) (u : Euclid (n + 1)) : Euclid (n + 1) :=
  ∑ e : Fin n, w e • (rootLinkD1 s (u e.castSucc) (u e.succ) • EuclideanSpace.single e.castSucc 1 +
    rootLinkD2 s (u e.castSucc) (u e.succ) • EuclideanSpace.single e.succ 1)

theorem weightedRootLinks_hasFDerivAt {n : ℕ} (s : ℝ) (w : Euclid n) (u : Euclid (n + 1)) :
    HasFDerivAt (weightedRootLinks s w) (innerSL ℝ (weightedRootGradient s w u)) u := by
  have hd : HasFDerivAt (weightedRootLinks s w)
      (∑ e : Fin n, w e • (rootLinkD1 s (u e.castSucc) (u e.succ) •
        EuclideanSpace.proj (𝕜 := ℝ) e.castSucc + rootLinkD2 s (u e.castSucc) (u e.succ) •
        EuclideanSpace.proj (𝕜 := ℝ) e.succ)) u := by
    apply HasFDerivAt.sum
    intro e _
    exact (rootLink_linear_hasFDerivAt s (EuclideanSpace.proj (𝕜 := ℝ) e.castSucc)
      (EuclideanSpace.proj (𝕜 := ℝ) e.succ) u).const_mul (w e)
  apply hd.congr_fderiv
  ext v
  simp [weightedRootGradient, innerSL_apply, sum_inner, inner_add_left,
    real_inner_smul_left, EuclideanSpace.inner_single_left, EuclideanSpace.proj, mul_add]

theorem weightedRootLinks_gradient {n : ℕ} (s : ℝ) (w : Euclid n) (u : Euclid (n + 1)) :
    gradient (weightedRootLinks s w) u = weightedRootGradient s w u :=
  (hasGradientAt_iff_hasFDerivAt.mpr (weightedRootLinks_hasFDerivAt s w u)).gradient

theorem weighted_adjacent_sum_left {n : ℕ} (w : Euclid n) (f : ℝ → ℝ → ℝ) (u : Euclid (n + 1)) :
    (∑ e : Fin n, (w e * f (u e.castSucc) (u e.succ)) • EuclideanSpace.single e.castSucc (1 : ℝ)) =
      pathPadLeft n (coordinateMultiplier (fun e => w e) (adjacentVector f u)) := by
  rw [← euclid_sum_single (coordinateMultiplier (fun e => w e) (adjacentVector f u)), map_sum]
  simp only [map_smul, pathPadLeft_single, coordinateMultiplier_apply, adjacentVector_apply]

theorem weighted_adjacent_sum_right {n : ℕ} (w : Euclid n) (f : ℝ → ℝ → ℝ) (u : Euclid (n + 1)) :
    (∑ e : Fin n, (w e * f (u e.castSucc) (u e.succ)) • EuclideanSpace.single e.succ (1 : ℝ)) =
      pathPadRight n (coordinateMultiplier (fun e => w e) (adjacentVector f u)) := by
  rw [← euclid_sum_single (coordinateMultiplier (fun e => w e) (adjacentVector f u)), map_sum]
  simp only [map_smul, pathPadRight_single, coordinateMultiplier_apply, adjacentVector_apply]

theorem weightedRootGradient_decomposition {n : ℕ} (s : ℝ) (w : Euclid n) (u : Euclid (n + 1)) :
    weightedRootGradient s w u =
      pathPadLeft n (coordinateMultiplier (fun e => w e) (adjacentVector (rootLinkD1 s) u)) +
      pathPadRight n (coordinateMultiplier (fun e => w e) (adjacentVector (rootLinkD2 s) u)) := by
  simp only [weightedRootGradient, smul_add, smul_smul, Finset.sum_add_distrib,
    weighted_adjacent_sum_left, weighted_adjacent_sum_right]

theorem weightedRootGradient_sub_norm {n : ℕ} {s W : ℝ} (hs : |s| = 1) (hW : 0 ≤ W)
    (w : Euclid n) (hw : ∀ e, |w e| ≤ W) (u v : Euclid (n + 1)) :
    ‖weightedRootGradient s w u - weightedRootGradient s w v‖ ≤ 4000 * W * ‖u - v‖ := by
  have h1 := (coordinateMultiplier_norm_bound (fun e => w e) hW hw
    (adjacentVector (rootLinkD1 s) u - adjacentVector (rootLinkD1 s) v)).trans
      (mul_le_mul_of_nonneg_left (rootLinkD1_adjacent_sub_norm hs u v) hW)
  have h2 := (coordinateMultiplier_norm_bound (fun e => w e) hW hw
    (adjacentVector (rootLinkD2 s) u - adjacentVector (rootLinkD2 s) v)).trans
      (mul_le_mul_of_nonneg_left (rootLinkD2_adjacent_sub_norm hs u v) hW)
  rw [weightedRootGradient_decomposition, weightedRootGradient_decomposition]
  calc
    _ = ‖pathPadLeft n (coordinateMultiplier (fun e => w e)
        (adjacentVector (rootLinkD1 s) u - adjacentVector (rootLinkD1 s) v)) +
      pathPadRight n (coordinateMultiplier (fun e => w e)
        (adjacentVector (rootLinkD2 s) u - adjacentVector (rootLinkD2 s) v))‖ := by
      congr 1; simp only [map_sub]; abel
    _ ≤ ‖coordinateMultiplier (fun e => w e)
        (adjacentVector (rootLinkD1 s) u - adjacentVector (rootLinkD1 s) v)‖ +
      ‖coordinateMultiplier (fun e => w e)
        (adjacentVector (rootLinkD2 s) u - adjacentVector (rootLinkD2 s) v)‖ := by
      simpa only [pathPadLeft_norm, pathPadRight_norm] using norm_add_le
        (pathPadLeft n (coordinateMultiplier (fun e => w e)
          (adjacentVector (rootLinkD1 s) u - adjacentVector (rootLinkD1 s) v)))
        (pathPadRight n (coordinateMultiplier (fun e => w e)
          (adjacentVector (rootLinkD2 s) u - adjacentVector (rootLinkD2 s) v)))
    _ ≤ _ := by nlinarith only [h1, h2]

end FreshGradientMinimax
