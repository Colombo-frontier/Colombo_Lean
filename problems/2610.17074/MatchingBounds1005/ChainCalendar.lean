import MatchingBounds1005.ChainOperatorFormula
import MatchingBounds1005.PathLayers

/-! # One-step propagation for the actual path-chain disclosure calendar -/
noncomputable section
open scoped BigOperators InnerProductSpace Matrix

namespace MatchingBounds1005.PathLayers
open BlockGeometry PathGreen

theorem initial_entry_disclosed (M n : ℕ) :
    blockVector M n 0 (entryVector M) ∈ layerSpace M n ((M + 2) / 2) 1 := by
  intro s j hj
  by_cases hs : s = 0
  · subst s
    by_cases hj0 : j = 0
    · subst j
      change 1 < layer ((M + 2) / 2) 0 0 at hj
      rw [layer_entry (by omega : 0 < (M + 2) / 2)] at hj
      simp at hj
    · simpa [blockVector, entryVector] using hj0
  · simp [blockVector, Pi.single_eq_of_ne hs]

theorem path_action_zero (L h : ℝ) (M jstar s t : ℕ)
    (z : EuclideanSpace ℝ (Fin (M + 1)))
    (hz : ∀ j, t < layer jstar s j.val → z j = 0)
    (i : Fin (M + 1)) (hi : t + 1 < layer jstar s i.val) :
    (pathMatrix L h M).toEuclideanLin z i = 0 := by
  change (∑ j, pathMatrix L h M i j * z j) = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : t < layer jstar s j.val
  · rw [hz j hj, mul_zero]
  · have hij : j.val + 1 < i.val := by
      by_contra hn
      have ha := layer_adjacent (jstar := jstar) (s := s) (Nat.le_of_not_gt hn)
      omega
    rw [pathMatrix_far_zero L h M i j (Or.inr hij), zero_mul]

theorem suffix_inner_zero (A : ℝ) (M n t : ℕ)
    (z : BlockSpace (E := EuclideanSpace ℝ (Fin (M + 1))) n)
    (hz : z ∈ layerSpace M n ((M + 2) / 2) t) (s : Fin (n + 1))
    (hs : t < (s.val + 1) * ((M + 2) / 2)) :
    ⟪suffixVector A M, z s⟫_ℝ = 0 := by
  change (∑ j, z s j * suffixVector A M j) = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val + 1 < (M + 2) / 2
  · rw [suffixVector_supported A M j hj, mul_zero]
  · rw [hz s j (by rw [layer_suffix (Nat.le_of_not_gt hj)]; exact hs), zero_mul]

theorem entry_inner_zero (M n t : ℕ)
    (z : BlockSpace (E := EuclideanSpace ℝ (Fin (M + 1))) n)
    (hz : z ∈ layerSpace M n ((M + 2) / 2) t) (s : Fin (n + 1))
    (hs : t < s.val * ((M + 2) / 2) + 1) :
    ⟪entryVector M, z s⟫_ℝ = 0 := by
  have hz0 := hz s 0 (by
    change t < layer ((M + 2) / 2) s.val 0
    rw [layer_entry (by omega : 0 < (M + 2) / 2)]
    exact hs)
  simpa [entryVector, PiLp.inner_apply] using hz0

theorem chainOperator_layer_propagation (L h A : ℝ) (M n t : ℕ)
    (G : BlockGeometry (EuclideanSpace ℝ (Fin (M + 1))))
    (hH : G.H = (pathMatrix L h M).toEuclideanLin)
    (ha : G.a = suffixVector A M) (he : G.e = entryVector M) :
    (layerSpace M n ((M + 2) / 2) t).map (G.chainOperator n).toLinearMap ≤
      layerSpace M n ((M + 2) / 2) (t + 1) := by
  rintro x ⟨z, hz, rfl⟩ s j hj
  have hH0 : G.H (z s) j = 0 := by
    rw [hH]
    exact path_action_zero L h M _ s.val t (z s) (hz s) j hj
  have hstab : ⟪G.a, z s⟫_ℝ * G.a j = 0 := by
    rw [ha]
    by_cases hjs : j.val + 1 < (M + 2) / 2
    · rw [suffixVector_supported A M j hjs, mul_zero]
    · have hs : t < (s.val + 1) * ((M + 2) / 2) := by
        rw [layer_suffix (Nat.le_of_not_gt hjs)] at hj
        omega
      rw [suffix_inner_zero A M n t z hz s hs, zero_mul]
  have hin : G.incomingHomogeneous z s * G.e j = 0 := by
    by_cases hj0 : j = 0
    · subst j
      have hs : t < s.val * ((M + 2) / 2) := by
        change t + 1 < layer ((M + 2) / 2) s.val 0 at hj
        rw [layer_entry (by omega : 0 < (M + 2) / 2)] at hj
        omega
      have hi0 : G.incomingHomogeneous z s = 0 := by
        unfold incomingHomogeneous
        apply Finset.sum_eq_zero
        intro q _
        split_ifs with hqs
        · rw [ha]
          apply suffix_inner_zero A M n t z hz
          have hv := congrArg Fin.val hqs
          change q.val + 1 = s.val at hv
          simpa only [Fin.coe_castSucc, hv] using hs
        · rfl
      rw [hi0, zero_mul]
    · have he0 : G.e j = 0 := by simp [he, entryVector, Pi.single_eq_of_ne hj0]
      rw [he0, mul_zero]
  have hout : G.outgoingEntry (fun i => z i) s * G.a j = 0 := by
    by_cases hjs : j.val + 1 < (M + 2) / 2
    · rw [ha, suffixVector_supported A M j hjs, mul_zero]
    · have hs : t < (s.val + 1) * ((M + 2) / 2) + 1 := by
        rw [layer_suffix (Nat.le_of_not_gt hjs)] at hj
        omega
      have ho0 : G.outgoingEntry (fun i => z i) s = 0 := by
        unfold outgoingEntry
        apply Finset.sum_eq_zero
        intro q _
        split_ifs with hqs
        · rw [he]
          apply entry_inner_zero M n t z hz
          have hv := congrArg Fin.val hqs
          change q.val = s.val at hv
          simpa only [Fin.val_succ, hv] using hs
        · rfl
      rw [ho0, zero_mul]
  change G.chainOperator n z s j = 0
  rw [G.chainOperator_apply]
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hH0]
  simp only [mul_assoc, hstab, hin, hout, mul_zero, zero_add, zero_sub, sub_zero]

theorem actual_chain_layer_propagation (L h A : ℝ) (hL : 0 < L) (hh : 0 < h)
    (hhsmall : h ≤ 1 / 4) (hA : 0 < A) (n t : ℕ) :
    (layerSpace (pathEdges h) n ((pathEdges h + 2) / 2) t).map
      ((actualBlockGeometry L h A hL hh hhsmall hA).chainOperator n).toLinearMap ≤
        layerSpace (pathEdges h) n ((pathEdges h + 2) / 2) (t + 1) :=
  chainOperator_layer_propagation L h A (pathEdges h) n t _ rfl rfl rfl

def copyLayerSpace (M n K jstar t : ℕ) : Submodule ℝ
    (CopySpace (E := EuclideanSpace ℝ (Fin (M + 1))) n K) :=
  (layerSpace M n jstar t).map (activeInsert n K).toLinearMap

theorem copyLayerSpace_mono (M n K jstar : ℕ) : Monotone (copyLayerSpace M n K jstar) := by
  intro t u htu
  exact Submodule.map_mono ((layerSpace_mono M n jstar) htu)

theorem copyLayerSpace_le_active (M n K jstar t : ℕ) :
    copyLayerSpace M n K jstar t ≤ activeSpace n K := by
  rintro x ⟨z, _, rfl⟩
  exact ⟨z, rfl⟩

theorem actual_copy_layer_propagation (L h A : ℝ) (hL : 0 < L) (hh : 0 < h)
    (hhsmall : h ≤ 1 / 4) (hA : 0 < A) (n K t : ℕ) :
    (copyLayerSpace (pathEdges h) n K ((pathEdges h + 2) / 2) t).map
      ((actualBlockGeometry L h A hL hh hhsmall hA).copyOperator n K).toLinearMap ≤
        copyLayerSpace (pathEdges h) n K ((pathEdges h + 2) / 2) (t + 1) := by
  rintro x ⟨z, ⟨v, hv, rfl⟩, rfl⟩
  refine ⟨(actualBlockGeometry L h A hL hh hhsmall hA).chainOperator n v, ?_, ?_⟩
  · exact actual_chain_layer_propagation L h A hL hh hhsmall hA n t ⟨v, hv, rfl⟩
  · exact ((actualBlockGeometry L h A hL hh hhsmall hA).copyOperator_activeInsert n K v).symm

theorem copy_readout_hidden (A : ℝ) (M n K t : ℕ) (s : Fin (n + 1))
    (ht : t < (s.val + 1) * ((M + 2) / 2)) :
    activeInsert n K (blockVector M n s (suffixVector A M)) ∈
      (copyLayerSpace M n K ((M + 2) / 2) t)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro x ⟨z, hz, rfl⟩
  change ⟪activeInsert n K z, activeInsert n K (blockVector M n s (suffixVector A M))⟫_ℝ = 0
  rw [(activeInsert (E := EuclideanSpace ℝ (Fin (M + 1))) n K).inner_map_map]
  exact (Submodule.mem_orthogonal _ _).mp (suffix_readout_hidden A M n t s ht) z hz

theorem copy_readout_disclosed (A : ℝ) (M n K t : ℕ) (s : Fin (n + 1))
    (ht : (s.val + 1) * ((M + 2) / 2) ≤ t) :
    activeInsert n K (blockVector M n s (suffixVector A M)) ∈
      copyLayerSpace M n K ((M + 2) / 2) t :=
  ⟨_, suffix_readout_mem A M n t s ht, rfl⟩

end MatchingBounds1005.PathLayers
