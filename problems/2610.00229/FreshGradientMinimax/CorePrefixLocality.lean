import FreshGradientMinimax.CoreTruncation

/-! Exact locality of the seed and the adjacent links under the static
threshold. The seed at the current stage is deliberately retained. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem coreSeed_prefix_value {n k : ℕ} (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k < i.val → |u i| ≤ 1 / 4) :
    weightedCoreSeed (coreSeedPrefix n (k + 1)) u = coreSeed u := by
  unfold weightedCoreSeed coreSeed squareLinkSeed
  congr 2
  apply Finset.sum_congr rfl
  intro e _
  change (if e.val < k + 1 then (1 : ℝ) else 0) * coreGate (u e.castSucc) = coreGate (u e.castSucc)
  by_cases he : e.val < k + 1
  · simp only [if_pos he, one_mul]
  · have hx := (abs_le.mp (hu e.castSucc (by change k < e.val; omega))).2
    rw [coreGate_zero (by linarith : u e.castSucc ≤ 1 / 2), mul_zero]

theorem coreSeed_prefix_gradient {n k : ℕ} (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k < i.val → |u i| ≤ 1 / 4) :
    weightedCoreSeedGradient (coreSeedPrefix n (k + 1)) u = coreSeedGradient u := by
  unfold weightedCoreSeedGradient coreSeedGradient
  congr 2
  apply Finset.sum_congr rfl
  intro e _
  change ((if e.val < k + 1 then (1 : ℝ) else 0) * coreGateDeriv (u e.castSucc)) • _ = _
  by_cases he : e.val < k + 1
  · simp only [if_pos he, one_mul]
  · have hx := (abs_le.mp (hu e.castSucc (by change k < e.val; omega))).2
    rw [(coreGate_derivatives_flat (by linarith : u e.castSucc ≤ 1 / 2)).1, mul_zero]

theorem rootLink_flat_small {s a : ℝ} (hs : |s| = 1) (ha : |a| ≤ 1 / 4) (b : ℝ) :
    rootLink s a b = 0 ∧ rootLinkD1 s a b = 0 ∧ rootLinkD2 s a b = 0 := by
  have h : s * a ≤ 1 / 2 := by
    have hh : |s * a| ≤ 1 / 4 := by simpa only [abs_mul, hs, one_mul] using ha
    linarith only [(abs_le.mp hh).2]
  have hf := rootLink_flat h b
  exact ⟨hf.1, hf.2.1, hf.2.2.1⟩

theorem sum_prefix_residual {n : ℕ} {G : Type*} [AddCommGroup G] (k : Fin n) (f : Fin n → G)
    (hf : ∀ e : Fin n, k.val < e.val → f e = 0) :
    (∑ e, f e) - (∑ e, if e.val < k.val then f e else 0) = f k := by
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · simp
  · intro e _ hne
    by_cases he : e.val < k.val
    · simp only [if_pos he, sub_self]
    · have hke : k.val < e.val := by
        have hv : e.val ≠ k.val := fun h => hne (Fin.ext h)
        omega
      simp only [if_neg he, hf e hke, sub_zero]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

def edgeWeightPrefix {n : ℕ} (k : ℕ) (w : Euclid n) : Euclid n :=
  (WithLp.equiv 2 _).symm (fun e : Fin n => if e.val < k then w e else 0)

theorem weightedRootLinks_prefix_residual {n : ℕ} {s : ℝ} (hs : |s| = 1)
    (k : Fin n) (w : Euclid n) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4) :
    weightedRootLinks s w u - weightedRootLinks s (edgeWeightPrefix k.val w) u =
      w k * rootLink s (u k.castSucc) (u k.succ) := by
  have hsum : weightedRootLinks s (edgeWeightPrefix k.val w) u =
      ∑ e : Fin n, if e.val < k.val then w e * rootLink s (u e.castSucc) (u e.succ) else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    change (if e.val < k.val then w e else 0) * _ = _
    split_ifs <;> simp only [zero_mul]
  rw [hsum]
  apply sum_prefix_residual
  intro e he
  rw [(rootLink_flat_small hs (hu e.castSucc he) (u e.succ)).1, mul_zero]

theorem weightedRootGradient_prefix_residual {n : ℕ} {s : ℝ} (hs : |s| = 1)
    (k : Fin n) (w : Euclid n) (u : Euclid (n + 1))
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4) :
    weightedRootGradient s w u - weightedRootGradient s (edgeWeightPrefix k.val w) u =
      w k • (rootLinkD1 s (u k.castSucc) (u k.succ) • EuclideanSpace.single k.castSucc 1 +
        rootLinkD2 s (u k.castSucc) (u k.succ) • EuclideanSpace.single k.succ 1) := by
  have hsum : weightedRootGradient s (edgeWeightPrefix k.val w) u =
      ∑ e : Fin n, if e.val < k.val then w e •
        (rootLinkD1 s (u e.castSucc) (u e.succ) • EuclideanSpace.single e.castSucc 1 +
          rootLinkD2 s (u e.castSucc) (u e.succ) • EuclideanSpace.single e.succ 1) else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    change (if e.val < k.val then w e else 0) • _ = _
    split_ifs <;> simp only [zero_smul]
  rw [hsum]
  apply sum_prefix_residual
  intro e he
  have hf := rootLink_flat_small hs (hu e.castSucc he) (u e.succ)
  simp only [hf.2.1, hf.2.2, zero_smul, zero_add, smul_zero]

end FreshGradientMinimax
