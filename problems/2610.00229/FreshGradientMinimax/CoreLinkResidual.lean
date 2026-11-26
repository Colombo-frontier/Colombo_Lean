import FreshGradientMinimax.CorePrefixLocality

/-! The actual interaction and its two gradients lose at most one edge under
the static prefix. Constants here are uniform in the ambient dimensions. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem coreLinkPrefix_left {n k : ℕ} (w : Euclid (n + n)) :
    euclidLeft (coordinateMultiplier (coreLinkPrefix n (k + 1)) w) =
      edgeWeightPrefix k (euclidLeft w) := by
  ext e
  simp [euclidLeft, coordinateMultiplier_apply, coreLinkPrefix, edgeWeightPrefix]

theorem coreLinkPrefix_right {n k : ℕ} (w : Euclid (n + n)) :
    euclidRight (coordinateMultiplier (coreLinkPrefix n (k + 1)) w) =
      edgeWeightPrefix k (euclidRight w) := by
  ext e
  change coreLinkPrefix n (k + 1) (e.natAdd n) * w (e.natAdd n) =
    if e.val < k then w (e.natAdd n) else 0
  simp only [coreLinkPrefix, Fin.addCases_right, Nat.add_lt_add_iff_right]
  split_ifs <;> simp only [one_mul, zero_mul]

theorem weightedRootLinks_prefix_bound {n : ℕ} {s r : ℝ} (hs : |s| = 1)
    (k : Fin n) (w : Euclid n) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4) (hw : |w k| ≤ r) :
    |weightedRootLinks s w u - weightedRootLinks s (edgeWeightPrefix k.val w) u| ≤ 4 * r := by
  rw [weightedRootLinks_prefix_residual hs k w u hu, abs_mul]
  have h := mul_le_mul hw (rootLink_component_bounds hs (u k.castSucc) (u k.succ)).1
    (abs_nonneg _) ((abs_nonneg _).trans hw)
  linarith only [h]

theorem weightedRootGradient_prefix_bound {n : ℕ} {s r : ℝ} (hs : |s| = 1)
    (k : Fin n) (w : Euclid n) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4) (hw : |w k| ≤ r) :
    ‖weightedRootGradient s w u - weightedRootGradient s (edgeWeightPrefix k.val w) u‖ ≤ 40 * r := by
  rw [weightedRootGradient_prefix_residual hs k w u hu, norm_smul, Real.norm_eq_abs]
  have hb := rootLink_component_bounds hs (u k.castSucc) (u k.succ)
  have hg : ‖rootLinkD1 s (u k.castSucc) (u k.succ) • EuclideanSpace.single k.castSucc (1 : ℝ) +
      rootLinkD2 s (u k.castSucc) (u k.succ) • EuclideanSpace.single k.succ (1 : ℝ)‖ ≤ 40 := by
    have h := norm_add_le
      (rootLinkD1 s (u k.castSucc) (u k.succ) • EuclideanSpace.single k.castSucc (1 : ℝ))
      (rootLinkD2 s (u k.castSucc) (u k.succ) • EuclideanSpace.single k.succ (1 : ℝ))
    simp only [norm_smul, Real.norm_eq_abs, EuclideanSpace.norm_single, norm_one, mul_one] at h
    linarith only [h, hb.2.1, hb.2.2.1]
  have h := mul_le_mul hw hg (norm_nonneg _) ((abs_nonneg _).trans hw)
  linarith only [h]

theorem weightedCoreLinks_prefix_bound {n : ℕ} {r : ℝ}
    (k : Fin n) (w : Euclid (n + n)) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4)
    (hwL : |w (k.castAdd n)| ≤ r) (hwR : |w (k.natAdd n)| ≤ r) :
    |weightedCoreLinks w u - weightedCoreLinks (coordinateMultiplier (coreLinkPrefix n (k.val + 1)) w) u|
      ≤ 8 * r := by
  have hL := weightedRootLinks_prefix_bound (by norm_num : |(-1 : ℝ)| = 1) k (euclidLeft w) u hu hwL
  have hR := weightedRootLinks_prefix_bound (by norm_num : |(1 : ℝ)| = 1) k (euclidRight w) u hu hwR
  rw [weightedCoreLinks_split, weightedCoreLinks_split, coreLinkPrefix_left, coreLinkPrefix_right]
  have he (a b c d : ℝ) : a + b - (c + d) = (a - c) + (b - d) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith only [hL, hR])

theorem coreLinksPullback_prefix_bound {n : ℕ} {r : ℝ}
    (k : Fin n) (w : Euclid (n + n)) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4)
    (hwL : |w (k.castAdd n)| ≤ r) (hwR : |w (k.natAdd n)| ≤ r) :
    ‖coreLinksPullback w u - coreLinksPullback (coordinateMultiplier (coreLinkPrefix n (k.val + 1)) w) u‖
      ≤ 80 * r := by
  have hL := weightedRootGradient_prefix_bound (by norm_num : |(-1 : ℝ)| = 1) k (euclidLeft w) u hu hwL
  have hR := weightedRootGradient_prefix_bound (by norm_num : |(1 : ℝ)| = 1) k (euclidRight w) u hu hwR
  rw [coreLinksPullback_split, coreLinksPullback_split, coreLinkPrefix_left, coreLinkPrefix_right]
  have he (a b c d : Euclid (n + 1)) : a + b - (c + d) = (a - c) + (b - d) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith only [hL, hR])

theorem edgeWeightPrefix_residual {n : ℕ} (k : Fin n) (v : Euclid n)
    (hv : ∀ e : Fin n, k.val < e.val → v e = 0) :
    v - edgeWeightPrefix k.val v = v k • EuclideanSpace.single k 1 := by
  ext e
  by_cases he : e = k
  · subst e
    simp [edgeWeightPrefix, EuclideanSpace.single_apply]
  · have hne : k ≠ e := Ne.symm he
    by_cases hlt : e.val < k.val
    · have hlt' : e < k := hlt
      simp [edgeWeightPrefix, EuclideanSpace.single_apply, hlt, hlt', hne, he]
    · have hgt : k.val < e.val := by
        have hvne : e.val ≠ k.val := fun h => he (Fin.ext h)
        omega
      have hlt' : ¬ e < k := hlt
      simp [edgeWeightPrefix, EuclideanSpace.single_apply, hlt, hlt', hne, he, hv e hgt]

theorem rootLinkVector_prefix_bound {n : ℕ} {s : ℝ} (hs : |s| = 1)
    (k : Fin n) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4) :
    ‖adjacentVector (rootLink s) u - edgeWeightPrefix k.val (adjacentVector (rootLink s) u)‖ ≤ 4 := by
  rw [edgeWeightPrefix_residual k (adjacentVector (rootLink s) u)
    (fun e he => (rootLink_flat_small hs (hu e.castSucc he) (u e.succ)).1)]
  simpa only [norm_smul, Real.norm_eq_abs, EuclideanSpace.norm_single, norm_one, mul_one,
    adjacentVector_apply] using (rootLink_component_bounds hs (u k.castSucc) (u k.succ)).1

theorem coreLinks_prefix_bound {n : ℕ} (k : Fin n) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4) :
    ‖coreLinks u - coordinateMultiplier (coreLinkPrefix n (k.val + 1)) (coreLinks u)‖ ≤ 8 := by
  have hL := rootLinkVector_prefix_bound (by norm_num : |(-1 : ℝ)| = 1) k u hu
  have hR := rootLinkVector_prefix_bound (by norm_num : |(1 : ℝ)| = 1) k u hu
  have he : coordinateMultiplier (coreLinkPrefix n (k.val + 1)) (coreLinks u) =
      euclidAppend (edgeWeightPrefix k.val (adjacentVector (rootLink (-1)) u))
        (edgeWeightPrefix k.val (adjacentVector (rootLink 1) u)) := by
    ext i
    refine Fin.addCases (fun e => ?_) (fun e => ?_) i
    · simp [coordinateMultiplier_apply, coreLinkPrefix, coreLinks, edgeWeightPrefix]
    · simp only [coordinateMultiplier_apply, coreLinkPrefix, Fin.addCases_right,
        Nat.add_lt_add_iff_right, coreLinks, euclidAppend_right]
      change (if e.val < k.val then (1 : ℝ) else 0) * _ = if e.val < k.val then _ else 0
      split_ifs <;> simp only [one_mul, zero_mul]
  rw [he, coreLinks, euclidAppend_sub]
  have hsq := euclidAppend_norm_sq
    (adjacentVector (rootLink (-1)) u - edgeWeightPrefix k.val (adjacentVector (rootLink (-1)) u))
    (adjacentVector (rootLink 1) u - edgeWeightPrefix k.val (adjacentVector (rootLink 1) u))
  nlinarith only [hsq, sq_nonneg (4 - ‖adjacentVector (rootLink (-1)) u -
    edgeWeightPrefix k.val (adjacentVector (rootLink (-1)) u)‖),
    pow_le_pow_left₀ (norm_nonneg _) hL 2, pow_le_pow_left₀ (norm_nonneg _) hR 2,
    norm_nonneg (euclidAppend
      (adjacentVector (rootLink (-1)) u - edgeWeightPrefix k.val (adjacentVector (rootLink (-1)) u))
      (adjacentVector (rootLink 1) u - edgeWeightPrefix k.val (adjacentVector (rootLink 1) u)))]

theorem coreInteraction_prefix_residual {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {a R r : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (k : Fin n) (u : Euclid (n + 1)) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4)
    (hyL : |frameCoordinates V y (k.castAdd n)| ≤ r) (hyR : |frameCoordinates V y (k.natAdd n)| ≤ r) :
    |coreInteraction V a R (fun _ => 1) u y - coreInteraction V a R (coreLinkPrefix n (k.val + 1)) u y|
      ≤ 8 * a * r := by
  unfold coreInteraction
  rw [coordinateMultiplier_one, ← mul_sub, abs_mul, abs_of_nonneg ha]
  have h := weightedCoreLinks_prefix_bound k (clipVector R (frameCoordinates V y)) u hu
    ((smoothClip_le_abs hR _).trans hyL) ((smoothClip_le_abs hR _).trans hyR)
  have hh := mul_le_mul_of_nonneg_left h ha
  linarith only [hh]

theorem coreInteractionGradU_prefix_residual {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {a R r : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (k : Fin n) (u : Euclid (n + 1)) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4)
    (hyL : |frameCoordinates V y (k.castAdd n)| ≤ r) (hyR : |frameCoordinates V y (k.natAdd n)| ≤ r) :
    ‖coreInteractionGradU V a R (fun _ => 1) u y - coreInteractionGradU V a R (coreLinkPrefix n (k.val + 1)) u y‖
      ≤ 80 * a * r := by
  unfold coreInteractionGradU
  rw [coordinateMultiplier_one, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have h := coreLinksPullback_prefix_bound k (clipVector R (frameCoordinates V y)) u hu
    ((smoothClip_le_abs hR _).trans hyL) ((smoothClip_le_abs hR _).trans hyR)
  have hh := mul_le_mul_of_nonneg_left h ha
  linarith only [hh]

theorem coreInteractionGradY_prefix_residual {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {a : ℝ} (ha : 0 ≤ a) (R : ℝ) (k : Fin n) (u : Euclid (n + 1)) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4) :
    ‖coreInteractionGradY V a R (fun _ => 1) u y - coreInteractionGradY V a R (coreLinkPrefix n (k.val + 1)) u y‖
      ≤ 8 * a := by
  unfold coreInteractionGradY
  rw [coordinateMultiplier_one, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha,
    ← map_sub, V.norm_map]
  have h := (weightedClipGradient_sub_weights R (coreLinks u)
    (coordinateMultiplier (coreLinkPrefix n (k.val + 1)) (coreLinks u)) (frameCoordinates V y)).trans
      (coreLinks_prefix_bound k u hu)
  have hh := mul_le_mul_of_nonneg_left h ha
  linarith only [hh]

end FreshGradientMinimax
