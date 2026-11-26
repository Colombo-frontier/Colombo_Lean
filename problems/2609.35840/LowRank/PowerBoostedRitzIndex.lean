import LowRank.PowerBoostedGapArithmetic

/-! A gap-free selected Ritz probability bound with polynomial decay in
the tail-to-head ratio, with one common tolerance across target indices. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem krylov_gaussian_power_boosted_ritz_index_confidence_le {a m l s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + l)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hp : ∀ j : Fin l, 0 < sp.value (j.natAdd m)) (hs : 2 * l + 2 ≤ s)
    (j : Fin l) (u : ℕ) {L δ q : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hq : 0 < q)
    (hl : ∀ i : Fin m, sp.value (i.castAdd l) ≤ L) (hj : L ≤ sp.value (j.natAdd m))
    (hn : chebyshevFilterDegree (powerBoostedGap δ u)
      (confidentRitzTolerance δ q s (m + l)) + u < n) :
    (iidMatrixLaw a s 1) {U |
      (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value (j.natAdd m) <
          sp.value (j.natAdd m) - (δ / 2) * L * (L / sp.value (j.natAdd m)) ^ (2 * u)} ≤
        ENNReal.ofReal (2 / q) := by
  let α := sp.value (j.natAdd m)
  let e := (δ / 2) * L * (L / α) ^ (2 * u)
  let t := α - e
  have hα : 0 < α := hL.trans_le hj
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hη := confidentRitzTolerance_pos (d := m + l) hδ hq (by omega : 0 < s)
  by_cases ht : 0 < t
  · have hr0 : 0 < l - j.val := Nat.sub_pos_of_lt j.isLt
    have hrl : l - j.val ≤ l := Nat.sub_le _ _
    have hr : l - j.val ≤ m + l := by omega
    let f := lastColumnIndex l (l - j.val) hrl
    have hi : lastColumnIndex (m + l) (l - j.val) hr ⟨0, hr0⟩ = j.natAdd m := by
      apply Fin.ext
      change m + l - (l - j.val) + 0 = m + j.val
      omega
    have hh (i : Fin (l - j.val)) : α ≤ sp.value ((f i).natAdd m) := by
      apply sp.increasing
      change m + j.val ≤ m + (l - (l - j.val) + i.val)
      omega
    have hbudget := powerBoostedTolerance_budget (s := s) (m := m) u hL.le hα.le
      (confidentRitzTolerance_budget hδ.le hq (by omega : 0 < s) (by omega : m ≤ m + l))
    have h := krylov_gaussian_selected_power_boosted_confidence_le hr0 hr A sp f
      (lastColumnIndex_injective l (l - j.val) hrl) hp hs u ht (sub_le_self _ he)
      (lt_min ht hL) (min_le_right t L) (powerBoostedGap_pos hδ u)
      (powerBoostedGap_le_one hδ1 u) hη hq hn hl
      (fun i hit => le_min hit.le (hl i)) hh (powerBoostedGap_cutoff u hδ hδ1 hL hj)
      (by simpa only [t, e, sub_sub_cancel] using hbudget)
    simpa only [hi, t, e, α] using h
  · have hsub : {U : Matrix (Fin a) (Fin s) ℝ |
        (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
          columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value (j.natAdd m) <
            sp.value (j.natAdd m) - (δ / 2) * L * (L / sp.value (j.natAdd m)) ^ (2 * u)} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro U hU
      have hnonneg := (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value_nonneg
          (rightGram_posSemidef _) (j.natAdd m)
      exact (not_lt_of_ge (le_trans (le_of_not_gt ht) hnonneg)) hU
    rw [hsub, measure_empty]
    exact zero_le _

end
end LowRank
