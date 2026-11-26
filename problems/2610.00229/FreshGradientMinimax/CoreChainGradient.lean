import FreshGradientMinimax.CoreLinkTermDerivative

/-! The actual Euclidean gradient of the scalar chain in (22). -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace

def coreChain {n : ℕ} (u : Euclid (n + 1)) : ℝ := squareLinkCore (fun i => u i)

def coreChainDerivative {n : ℕ} (u : Euclid (n + 1)) : Euclid (n + 1) →L[ℝ] ℝ :=
  -coreDensity (u 0) • EuclideanSpace.proj (𝕜 := ℝ) 0 + ∑ e : Fin n,
    (coreLinkTermD1 (u e.castSucc) (u e.succ) • EuclideanSpace.proj (𝕜 := ℝ) e.castSucc +
      coreLinkTermD2 (u e.castSucc) (u e.succ) • EuclideanSpace.proj (𝕜 := ℝ) e.succ)

def coreChainGradient {n : ℕ} (u : Euclid (n + 1)) : Euclid (n + 1) :=
  -coreDensity (u 0) • EuclideanSpace.single 0 1 + ∑ e : Fin n,
    (coreLinkTermD1 (u e.castSucc) (u e.succ) • EuclideanSpace.single e.castSucc 1 +
      coreLinkTermD2 (u e.castSucc) (u e.succ) • EuclideanSpace.single e.succ 1)

theorem coreChain_hasFDerivAt {n : ℕ} (u : Euclid (n + 1)) :
    HasFDerivAt coreChain (coreChainDerivative u) u := by
  have hseed := ((coreTheta_hasDerivAt (u 0)).comp_hasFDerivAt u
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))).hasFDerivAt).neg
  have hsum : HasFDerivAt (fun v : Euclid (n + 1) =>
      ∑ e : Fin n, coreLinkTerm (v e.castSucc) (v e.succ))
      (∑ e : Fin n, (coreLinkTermD1 (u e.castSucc) (u e.succ) • EuclideanSpace.proj (𝕜 := ℝ) e.castSucc +
        coreLinkTermD2 (u e.castSucc) (u e.succ) • EuclideanSpace.proj (𝕜 := ℝ) e.succ)) u := by
    apply HasFDerivAt.sum
    intro e _
    exact coreLinkTerm_linear_hasFDerivAt
      (EuclideanSpace.proj (𝕜 := ℝ) e.castSucc)
      (EuclideanSpace.proj (𝕜 := ℝ) e.succ) u
  convert hseed.add hsum using 1
  simp only [coreChainDerivative, neg_smul]

theorem coreChainDerivative_eq_inner {n : ℕ} (u : Euclid (n + 1)) :
    coreChainDerivative u = innerSL ℝ (coreChainGradient u) := by
  ext v
  simp [coreChainDerivative, coreChainGradient, innerSL_apply, inner_add_left, sum_inner,
    real_inner_smul_left, EuclideanSpace.inner_single_left, EuclideanSpace.proj]

theorem coreChain_gradient {n : ℕ} (u : Euclid (n + 1)) : gradient coreChain u = coreChainGradient u := by
  have hd := coreChain_hasFDerivAt u
  rw [coreChainDerivative_eq_inner] at hd
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient

theorem coreChainGradient_apply {n : ℕ} (u : Euclid (n + 1)) (j : Fin (n + 1)) :
    coreChainGradient u j = (if (0 : Fin (n + 1)) = j then -coreDensity (u 0) else 0) +
      ∑ e : Fin n, ((if e.castSucc = j then coreLinkTermD1 (u e.castSucc) (u e.succ) else 0) +
        if e.succ = j then coreLinkTermD2 (u e.castSucc) (u e.succ) else 0) := by
  change (EuclideanSpace.proj (𝕜 := ℝ) j) (coreChainGradient u) = _
  unfold coreChainGradient
  rw [map_add, map_smul, map_sum]
  simp [EuclideanSpace.proj, EuclideanSpace.single_apply, eq_comm]

theorem coreChainGradient_nonpos {n : ℕ} (u : Euclid (n + 1)) (j : Fin (n + 1)) :
    coreChainGradient u j ≤ 0 := by
  rw [coreChainGradient_apply]
  apply add_nonpos
  · split_ifs
    · exact neg_nonpos.mpr (coreDensity_pos _).le
    · rfl
  · apply Finset.sum_nonpos
    intro e _
    apply add_nonpos
    · split_ifs
      · exact coreLinkTermD1_nonpos _ _
      · rfl
    · split_ifs
      · exact coreLinkTermD2_nonpos _ _
      · rfl

theorem coreChainGradient_seed_le {n : ℕ} (u : Euclid (n + 1)) :
    coreChainGradient u 0 ≤ -coreDensity (u 0) := by
  rw [coreChainGradient_apply, if_pos rfl]
  apply add_le_of_nonpos_right
  apply Finset.sum_nonpos
  intro e _
  apply add_nonpos
  · split_ifs
    · exact coreLinkTermD1_nonpos _ _
    · rfl
  · split_ifs
    · exact coreLinkTermD2_nonpos _ _
    · rfl

theorem coreChainGradient_incoming_le {n : ℕ} (u : Euclid (n + 1)) (i : Fin n) :
    coreChainGradient u i.succ ≤ coreLinkTermD2 (u i.castSucc) (u i.succ) := by
  rw [coreChainGradient_apply]
  have hz : (0 : Fin (n + 1)) ≠ i.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  rw [if_neg hz, zero_add]
  have hi : i.castSucc ≠ i.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  calc
    _ ≤ ∑ e : Fin n, if e = i then coreLinkTermD2 (u i.castSucc) (u i.succ) else 0 := by
      apply Finset.sum_le_sum
      intro e _
      by_cases he : e = i
      · subst e
        simp only [if_neg hi, if_pos rfl, zero_add, le_refl]
      · rw [if_neg he]
        apply add_nonpos
        · split_ifs
          · exact coreLinkTermD1_nonpos _ _
          · rfl
        · split_ifs
          · exact coreLinkTermD2_nonpos _ _
          · rfl
    _ = _ := by simp

end FreshGradientMinimax
