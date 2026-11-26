import FreshGradientMinimax.CoreTruncation

/-! The scalar truncated objective depends only on its displayed primal and
dual prefix. Equality of scalar functions will also identify their true gradients. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace

def corePrimalPrefix {m : ℕ} (j : ℕ) : Euclid m →L[ℝ] Euclid m :=
  coordinateMultiplier (fun i => if i.val < j then 1 else 0)

@[simp]
theorem corePrimalPrefix_apply {m : ℕ} (j : ℕ) (u : Euclid m) (i : Fin m) :
    corePrimalPrefix j u i = if i.val < j then u i else 0 := by
  simp only [corePrimalPrefix, coordinateMultiplier_apply]
  split_ifs <;> simp only [one_mul, zero_mul]

theorem corePrimalPrefix_known {m j : ℕ} (u : Euclid m) (i : Fin m) (hi : i.val < j) :
    corePrimalPrefix j u i = u i := by rw [corePrimalPrefix_apply, if_pos hi]

theorem corePrimalPrefix_nested {m j J : ℕ} (h : j ≤ J) (u : Euclid m) :
    corePrimalPrefix j (corePrimalPrefix J u) = corePrimalPrefix j u := by
  ext i
  simp only [corePrimalPrefix_apply]
  by_cases hi : i.val < j
  · simp only [if_pos hi, if_pos (lt_of_lt_of_le hi h)]
  · simp only [if_neg hi]

theorem coreLinkPrefix_nested {n j J : ℕ} (h : j ≤ J) (v : Euclid (n + n)) :
    coordinateMultiplier (coreLinkPrefix n j) (coordinateMultiplier (coreLinkPrefix n J) v) =
      coordinateMultiplier (coreLinkPrefix n j) v := by
  ext i
  refine Fin.addCases (fun e => ?_) (fun e => ?_) i
  · simp only [coordinateMultiplier_apply, coreLinkPrefix, Fin.addCases_left]
    by_cases he : e.val + 1 < j
    · rw [if_pos he, if_pos (lt_of_lt_of_le he h), one_mul]
    · simp only [if_neg he, zero_mul]
  · simp only [coordinateMultiplier_apply, coreLinkPrefix, Fin.addCases_right]
    by_cases he : e.val + 1 < j
    · rw [if_pos he, if_pos (lt_of_lt_of_le he h), one_mul]
    · simp only [if_neg he, zero_mul]

theorem coreSeed_prefix_congr {n j : ℕ} (hj : 0 < j) (u v : Euclid (n + 1))
    (h : ∀ i : Fin (n + 1), i.val < j → u i = v i) :
    weightedCoreSeed (coreSeedPrefix n j) u = weightedCoreSeed (coreSeedPrefix n j) v := by
  unfold weightedCoreSeed
  rw [h 0 hj]
  congr 2
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e.val < j
  · rw [h e.castSucc he]
  · change (if e.val < j then (1 : ℝ) else 0) * _ = (if e.val < j then (1 : ℝ) else 0) * _
    simp only [if_neg he, zero_mul]

theorem coreSeed_prefix_read {n j : ℕ} (hj : 0 < j) (u : Euclid (n + 1)) :
    weightedCoreSeed (coreSeedPrefix n j) (corePrimalPrefix j u) = weightedCoreSeed (coreSeedPrefix n j) u :=
  coreSeed_prefix_congr hj _ _ (corePrimalPrefix_known u)

theorem coreLinks_prefix_congr {n j : ℕ} (u v : Euclid (n + 1))
    (h : ∀ i : Fin (n + 1), i.val < j → u i = v i) :
    coordinateMultiplier (coreLinkPrefix n j) (coreLinks u) =
      coordinateMultiplier (coreLinkPrefix n j) (coreLinks v) := by
  ext i
  refine Fin.addCases (fun e => ?_) (fun e => ?_) i
  · simp only [coordinateMultiplier_apply, coreLinkPrefix, Fin.addCases_left, coreLinks_plus]
    by_cases he : e.val + 1 < j
    · rw [h e.castSucc (by change e.val < j; omega), h e.succ he]
    · simp only [if_neg he, zero_mul]
  · simp only [coordinateMultiplier_apply, coreLinkPrefix, Fin.addCases_right, coreLinks_minus]
    by_cases he : e.val + 1 < j
    · rw [h e.castSucc (by change e.val < j; omega), h e.succ he]
    · simp only [if_neg he, zero_mul]

theorem weightedCoreLinks_prefix_congr {n j : ℕ} (w : Euclid (n + n)) (u v : Euclid (n + 1))
    (h : ∀ i : Fin (n + 1), i.val < j → u i = v i) :
    weightedCoreLinks (coordinateMultiplier (coreLinkPrefix n j) w) u =
      weightedCoreLinks (coordinateMultiplier (coreLinkPrefix n j) w) v := by
  unfold weightedCoreLinks
  rw [coordinateMultiplier_inner_comm _ w (coreLinks u),
    coordinateMultiplier_inner_comm _ w (coreLinks v), coreLinks_prefix_congr u v h]

theorem clipVector_prefix_read {n : ℕ} (j : ℕ) (R : ℝ) (v : Euclid (n + n)) :
    coordinateMultiplier (coreLinkPrefix n j) (clipVector R (coordinateMultiplier (coreLinkPrefix n j) v)) =
      coordinateMultiplier (coreLinkPrefix n j) (clipVector R v) := by
  ext i
  refine Fin.addCases (fun e => ?_) (fun e => ?_) i
  · simp only [coordinateMultiplier_apply, clipVector_apply, coreLinkPrefix, Fin.addCases_left]
    split_ifs <;> simp only [one_mul, zero_mul]
  · simp only [coordinateMultiplier_apply, clipVector_apply, coreLinkPrefix, Fin.addCases_right]
    split_ifs <;> simp only [one_mul, zero_mul]

def primalPrefixRead {m d : ℕ} (j : ℕ) (A : Euclid d →L[ℝ] Euclid m) : Euclid d →L[ℝ] Euclid m :=
  (corePrimalPrefix j).comp A

def dualPrefixRead {n d : ℕ} (j : ℕ) (B : Euclid d →L[ℝ] Euclid (n + n)) : Euclid d →L[ℝ] Euclid (n + n) :=
  (coordinateMultiplier (coreLinkPrefix n j)).comp B

theorem primalPrefixRead_congr {m d j : ℕ} (A A' : Euclid d →L[ℝ] Euclid m)
    (h : ∀ i : Fin m, i.val < j → ∀ x, A x i = A' x i) : primalPrefixRead j A = primalPrefixRead j A' := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp only [primalPrefixRead, ContinuousLinearMap.comp_apply, corePrimalPrefix_apply]
  split_ifs with hi
  · exact h i hi x
  · rfl

theorem dualPrefixRead_congr {n d j : ℕ} (B B' : Euclid d →L[ℝ] Euclid (n + n))
    (h : ∀ e : Fin n, e.val + 1 < j → ∀ y,
      B y (e.castAdd n) = B' y (e.castAdd n) ∧ B y (e.natAdd n) = B' y (e.natAdd n)) :
    dualPrefixRead j B = dualPrefixRead j B' := by
  apply ContinuousLinearMap.ext
  intro y
  ext i
  refine Fin.addCases (fun e => ?_) (fun e => ?_) i
  · simp only [dualPrefixRead, ContinuousLinearMap.comp_apply, coordinateMultiplier_apply,
      coreLinkPrefix, Fin.addCases_left]
    split_ifs with he
    · rw [(h e he y).1]
    · simp only [zero_mul]
  · simp only [dualPrefixRead, ContinuousLinearMap.comp_apply, coordinateMultiplier_apply,
      coreLinkPrefix, Fin.addCases_right]
    split_ifs with he
    · rw [(h e he y).2]
    · simp only [zero_mul]

theorem primalPrefixRead_nested {m d j J : ℕ} (h : j ≤ J) (A : Euclid d →L[ℝ] Euclid m) :
    primalPrefixRead j (primalPrefixRead J A) = primalPrefixRead j A := by
  apply ContinuousLinearMap.ext
  intro x
  exact corePrimalPrefix_nested h (A x)

theorem dualPrefixRead_nested {n d j J : ℕ} (h : j ≤ J) (B : Euclid d →L[ℝ] Euclid (n + n)) :
    dualPrefixRead j (dualPrefixRead J B) = dualPrefixRead j B := by
  apply ContinuousLinearMap.ext
  intro y
  exact coreLinkPrefix_nested h (B y)

end FreshGradientMinimax
