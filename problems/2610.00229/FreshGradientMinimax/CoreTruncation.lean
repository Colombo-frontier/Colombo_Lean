import FreshGradientMinimax.MaskedCoreSmooth

/-! The paper's precise prefix convention: seed i <= j is retained, whereas
link i is indexed from 2 and retained exactly when i <= j. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def coreSeedPrefix (n j : ℕ) : Euclid n :=
  (WithLp.equiv 2 _).symm (fun e : Fin n => if e.val < j then 1 else 0)

def coreLinkPrefix (n j : ℕ) : Fin (n + n) → ℝ :=
  Fin.addCases (fun e : Fin n => if e.val + 1 < j then 1 else 0)
    (fun e : Fin n => if e.val + 1 < j then 1 else 0)

def truncatedCoreObjective {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (μ t : ℝ) (j : ℕ) := maskedCoreObjective V μ t (coreSeedPrefix n j) (coreLinkPrefix n j)

def paperTruncatedCore {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (μ lam : ℝ) (j : ℕ) := truncatedCoreObjective V μ (Real.sqrt (lam / μ)) j

theorem coreSeedPrefix_bound (n j : ℕ) (e : Fin n) : |coreSeedPrefix n j e| ≤ 1 := by
  change |if e.val < j then (1 : ℝ) else 0| ≤ 1
  split_ifs <;> norm_num

theorem coreLinkPrefix_bound (n j : ℕ) (e : Fin (n + n)) : |coreLinkPrefix n j e| ≤ 1 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) e
  · simp only [coreLinkPrefix, Fin.addCases_left]
    split_ifs <;> norm_num
  · simp only [coreLinkPrefix, Fin.addCases_right]
    split_ifs <;> norm_num

theorem coreSeedPrefix_full (n : ℕ) : coreSeedPrefix n (n + 1) = (WithLp.equiv 2 _).symm (fun _ => (1 : ℝ)) := by
  ext e
  change (if e.val < n + 1 then (1 : ℝ) else 0) = 1
  exact if_pos (by omega)

theorem coreLinkPrefix_full (n : ℕ) : coreLinkPrefix n (n + 1) = fun _ => 1 := by
  funext e
  refine Fin.addCases (fun i => ?_) (fun i => ?_) e
  · simp only [coreLinkPrefix, Fin.addCases_left]
    exact if_pos (by omega)
  · simp only [coreLinkPrefix, Fin.addCases_right]
    exact if_pos (by omega)

theorem truncatedCoreObjective_full {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ t : ℝ) :
    truncatedCoreObjective V μ t (n + 1) = coreProtectedObjective V μ t := by
  rw [truncatedCoreObjective, coreSeedPrefix_full, coreLinkPrefix_full, maskedCore_full]

theorem paperTruncatedCore_full {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy) (μ lam : ℝ) :
    paperTruncatedCore V μ lam (n + 1) = paperCoreObjective V μ lam :=
  truncatedCoreObjective_full V μ _

theorem truncatedSeed_formula (n j : ℕ) (u : Euclid (n + 1)) :
    weightedCoreSeed (coreSeedPrefix n j) u = -coreTheta (u 0) - coreThetaMass *
      ∑ e : Fin n, if e.val < j then coreGate (u e.castSucc) else 0 := by
  unfold weightedCoreSeed
  congr 2
  apply Finset.sum_congr rfl
  intro e _
  change (if e.val < j then (1 : ℝ) else 0) * _ = _
  split_ifs <;> simp

theorem truncatedInteraction_formula {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (a R : ℝ) (j : ℕ) (u : Euclid (n + 1)) (y : Euclid dy) :
    coreInteraction V a R (coreLinkPrefix n j) u y = a *
      ((∑ e : Fin n, if e.val + 1 < j then
        smoothClip R (frameCoordinates V y (e.castAdd n)) * coreLinkPlus (u e.castSucc) (u e.succ) else 0) +
       (∑ e : Fin n, if e.val + 1 < j then
        smoothClip R (frameCoordinates V y (e.natAdd n)) * coreLinkMinus (u e.castSucc) (u e.succ) else 0)) := by
  unfold coreInteraction weightedCoreLinks
  rw [PiLp.inner_apply, Fin.sum_univ_add]
  congr 1
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro e _
    simp only [RCLike.inner_apply', starRingEnd_apply, star_trivial, coordinateMultiplier_apply,
      coreLinkPrefix, Fin.addCases_left, clipVector, coreLinks_plus]
    change (if e.val + 1 < j then (1 : ℝ) else 0) *
      smoothClip R (frameCoordinates V y (e.castAdd n)) * coreLinkPlus (u e.castSucc) (u e.succ) = _
    split_ifs <;> simp only [one_mul, zero_mul]
  · apply Finset.sum_congr rfl
    intro e _
    simp only [RCLike.inner_apply', starRingEnd_apply, star_trivial, coordinateMultiplier_apply,
      coreLinkPrefix, Fin.addCases_right, clipVector, coreLinks_minus]
    change (if e.val + 1 < j then (1 : ℝ) else 0) *
      smoothClip R (frameCoordinates V y (e.natAdd n)) * coreLinkMinus (u e.castSucc) (u e.succ) = _
    split_ifs <;> simp only [one_mul, zero_mul]

end FreshGradientMinimax
