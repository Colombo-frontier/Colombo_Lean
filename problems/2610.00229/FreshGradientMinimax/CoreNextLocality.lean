import FreshGradientMinimax.CoreTruncationResidual

/-! Revealing one additional primal stage and its two dual columns makes
the truncated gradient equal to the full gradient on the good primal event. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem weightedRootLinks_next_eq {n : ℕ} {s : ℝ} (hs : |s| = 1)
    (k : ℕ) (w : Euclid n) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k < i.val → |u i| ≤ 1 / 4) :
    weightedRootLinks s (edgeWeightPrefix (k + 1) w) u = weightedRootLinks s w u := by
  apply Finset.sum_congr rfl
  intro e _
  change (if e.val < k + 1 then w e else 0) * _ = w e * _
  by_cases he : e.val < k + 1
  · rw [if_pos he]
  · rw [(rootLink_flat_small hs (hu e.castSucc (by change k < e.val; omega)) (u e.succ)).1]
    simp only [mul_zero]

theorem weightedRootGradient_next_eq {n : ℕ} {s : ℝ} (hs : |s| = 1)
    (k : ℕ) (w : Euclid n) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k < i.val → |u i| ≤ 1 / 4) :
    weightedRootGradient s (edgeWeightPrefix (k + 1) w) u = weightedRootGradient s w u := by
  apply Finset.sum_congr rfl
  intro e _
  change (if e.val < k + 1 then w e else 0) • _ = w e • _
  by_cases he : e.val < k + 1
  · rw [if_pos he]
  · have hf := rootLink_flat_small hs (hu e.castSucc (by change k < e.val; omega)) (u e.succ)
    simp only [hf.2.1, hf.2.2, zero_smul, zero_add, smul_zero]

theorem rootLinkVector_next_eq {n : ℕ} {s : ℝ} (hs : |s| = 1) (k : ℕ) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k < i.val → |u i| ≤ 1 / 4) :
    edgeWeightPrefix (k + 1) (adjacentVector (rootLink s) u) = adjacentVector (rootLink s) u := by
  ext e
  change (if e.val < k + 1 then rootLink s (u e.castSucc) (u e.succ) else 0) = _
  by_cases he : e.val < k + 1
  · exact if_pos he
  · rw [if_neg he]
    exact (rootLink_flat_small hs (hu e.castSucc (by change k < e.val; omega)) (u e.succ)).1.symm

theorem coreLinks_next_eq {n : ℕ} (k : ℕ) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k < i.val → |u i| ≤ 1 / 4) :
    coordinateMultiplier (coreLinkPrefix n (k + 2)) (coreLinks u) = coreLinks u := by
  have hL0 : euclidLeft (coreLinks u) = adjacentVector (rootLink (-1)) u := by
    ext e
    exact euclidAppend_left _ _ e
  have hR0 : euclidRight (coreLinks u) = adjacentVector (rootLink 1) u := by
    ext e
    exact euclidAppend_right _ _ e
  have hL : euclidLeft (coordinateMultiplier (coreLinkPrefix n (k + 2)) (coreLinks u)) = euclidLeft (coreLinks u) := by
    rw [show k + 2 = (k + 1) + 1 by omega, coreLinkPrefix_left, hL0]
    exact rootLinkVector_next_eq (by norm_num) k u hu
  have hR : euclidRight (coordinateMultiplier (coreLinkPrefix n (k + 2)) (coreLinks u)) = euclidRight (coreLinks u) := by
    rw [show k + 2 = (k + 1) + 1 by omega, coreLinkPrefix_right, hR0]
    exact rootLinkVector_next_eq (by norm_num) k u hu
  calc
    _ = euclidAppend (euclidLeft (coordinateMultiplier (coreLinkPrefix n (k + 2)) (coreLinks u)))
        (euclidRight (coordinateMultiplier (coreLinkPrefix n (k + 2)) (coreLinks u))) := (euclidAppend_blocks _).symm
    _ = coreLinks u := by rw [hL, hR, euclidAppend_blocks]

theorem weightedCoreLinks_next_eq {n : ℕ} (k : ℕ) (w : Euclid (n + n)) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k < i.val → |u i| ≤ 1 / 4) :
    weightedCoreLinks (coordinateMultiplier (coreLinkPrefix n (k + 2)) w) u = weightedCoreLinks w u := by
  rw [weightedCoreLinks_split, weightedCoreLinks_split,
    show k + 2 = (k + 1) + 1 by omega, coreLinkPrefix_left, coreLinkPrefix_right,
    weightedRootLinks_next_eq (by norm_num : |(-1 : ℝ)| = 1) k _ u hu,
    weightedRootLinks_next_eq (by norm_num : |(1 : ℝ)| = 1) k _ u hu]

theorem coreLinksPullback_next_eq {n : ℕ} (k : ℕ) (w : Euclid (n + n)) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k < i.val → |u i| ≤ 1 / 4) :
    coreLinksPullback (coordinateMultiplier (coreLinkPrefix n (k + 2)) w) u = coreLinksPullback w u := by
  rw [coreLinksPullback_split, coreLinksPullback_split,
    show k + 2 = (k + 1) + 1 by omega, coreLinkPrefix_left, coreLinkPrefix_right,
    weightedRootGradient_next_eq (by norm_num : |(-1 : ℝ)| = 1) k _ u hu,
    weightedRootGradient_next_eq (by norm_num : |(1 : ℝ)| = 1) k _ u hu]

theorem coreInteraction_next_eq {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (a R : ℝ) (k : ℕ) (u : Euclid (n + 1)) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k < i.val → |u i| ≤ 1 / 4) :
    coreInteraction V a R (coreLinkPrefix n (k + 2)) u y = coreInteraction V a R (fun _ => 1) u y ∧
    coreInteractionGradU V a R (coreLinkPrefix n (k + 2)) u y = coreInteractionGradU V a R (fun _ => 1) u y ∧
    coreInteractionGradY V a R (coreLinkPrefix n (k + 2)) u y = coreInteractionGradY V a R (fun _ => 1) u y := by
  simp only [coreInteraction, coreInteractionGradU, coreInteractionGradY, coordinateMultiplier_one,
    weightedCoreLinks_next_eq k _ u hu, coreLinksPullback_next_eq k _ u hu, coreLinks_next_eq k u hu, and_self]

theorem truncatedCore_next_gradients_eq {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (k : ℕ) (u : Euclid (n + 1)) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k < i.val → |u i| ≤ 1 / 4) :
    gradient (fun v => truncatedCoreObjective V μ t (k + 2) v y) u =
      gradient (fun v => coreProtectedObjective V μ t v y) u ∧
    gradient (truncatedCoreObjective V μ t (k + 2) u) y = gradient (coreProtectedObjective V μ t u) y := by
  have h := coreInteraction_next_eq V (2 * μ * t) (32 * t) k u y hu
  have hb : coreProtectedWeight V μ t (coreLinkPrefix n (k + 2)) u y =
      coreProtectedWeight V μ t (fun _ => 1) u y := by
    simp only [coreProtectedWeight, coreProtectedQ, h.1]
  have hs : weightedCoreSeedGradient (coreSeedPrefix n (k + 2)) u = coreSeedGradient u :=
    coreSeed_prefix_gradient u (fun i hi => hu i (by omega))
  simp only [truncatedCoreObjective, maskedCore_gradient_u V hμ ht, maskedCore_gradient_y V hμ ht,
    coreProtectedObjective_gradient_u V hμ ht, coreProtectedObjective_gradient_y V hμ ht,
    maskedCoreGradU, maskedCoreGradY, coreProtectedGradU, coreProtectedGradY, hs,
    coreProtectedCapGradU, coreProtectedCapGradY, coreProtectedQGradY, hb, h.2.1, h.2.2, and_self]

end FreshGradientMinimax
