import LowRank.GapAccuracyConfidence
import LowRank.UnconditionalTailRitz

/-! A larger inverted head block can serve fewer requested output columns.
The gap is fixed while the error tolerance is independently adjustable. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators ENNReal
noncomputable section

theorem lastColumnIndex_natAdd (m l k : ℕ) (hkl : k ≤ l) (hkd : k ≤ m + l) (j : Fin k) :
    (lastColumnIndex l k hkl j).natAdd m = lastColumnIndex (m + l) k hkd j := by
  apply Fin.ext
  change m + (l - k + j.val) = m + l - k + j.val
  omega

theorem krylov_wide_gap_ritz_confidence_le {a m l k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + l)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hkl : k ≤ l)
    (hp : ∀ j : Fin l, 0 < sp.value (j.natAdd m)) (hs : 2 * l + 2 ≤ s)
    {L T δ q : ℝ} (hL : 0 < L) (hLT : L ≤ T) (hδ : 0 < δ) (hq : 0 < q)
    (hl : ∀ i : Fin m, sp.value (i.castAdd l) ≤ L)
    (hgap : ∀ j : Fin k, L * (1 + (1 : ℝ) / 2) ≤ sp.value (lastColumnIndex (m + l) k (by omega) j))
    (hn : chebyshevFilterDegree 1 (confidentRitzTolerance (2 * δ) q s (m + l)) < n) :
    (iidMatrixLaw a s 1) (krylovTailRitzEvent A sp k s n (by omega) (2 * δ) T)ᶜ ≤
      ENNReal.ofReal ((k : ℝ) * (2 / q)) := by
  have hT : 0 ≤ T := hL.le.trans hLT
  have hη := confidentRitzTolerance_pos (d := m + l) (by positivity : 0 < 2 * δ) hq (by omega : 0 < s)
  have hb := confidentRitzTolerance_budget (by positivity : 0 ≤ 2 * δ) hq
    (by omega : 0 < s) (by omega : m ≤ m + l)
  rw [show (2 * δ) / 2 = δ by ring] at hb
  have hbudget : confidentRitzTolerance (2 * δ) q s (m + l) ^ 2 *
      (q ^ 2 * (s : ℝ) * (m : ℝ)) * L ≤ δ * T :=
    (mul_le_mul_of_nonneg_right hb hL.le).trans (mul_le_mul_of_nonneg_left hLT hδ.le)
  let E : Fin k → Set (Matrix (Fin a) (Fin s) ℝ) := fun j => {U |
    (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
        (lastColumnIndex (m + l) k (by omega) j) <
          sp.value (lastColumnIndex (m + l) k (by omega) j) - δ * T}
  have he : (krylovTailRitzEvent A sp k s n (by omega) (2 * δ) T)ᶜ = ⋃ j : Fin k, E j := by
    ext U
    simp only [krylovTailRitzEvent, E, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_iUnion, not_forall, not_le, show (2 * δ) / 2 = δ by ring]
  have hE (j : Fin k) : (iidMatrixLaw a s 1) (E j) ≤ ENNReal.ofReal (2 / q) := by
    have hi := lastColumnIndex_natAdd m l k hkl (by omega) j
    have h := krylov_gaussian_gap_ritz_index_confidence_le A sp hp hs
      (lastColumnIndex l k hkl j) hL (mul_nonneg hδ.le hT) hl (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) ≤ 1) hη hq hn
      (by simpa only [hi] using hgap j) hbudget
    simpa only [E, hi] using h
  rw [he]
  calc
    _ ≤ ∑ j : Fin k, (iidMatrixLaw a s 1) (E j) := by
      simpa only [tsum_fintype] using measure_iUnion_le E
    _ ≤ ∑ _ : Fin k, ENNReal.ofReal (2 / q) := Finset.sum_le_sum (fun j _ => hE j)
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun (_ : Fin k) _ => by positivity :
        ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ (2 : ℝ) / q)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem krylov_wide_tail_gap_confidence_le {a m l k s n : ℕ} (hm : 0 < m)
    (A : Matrix (Fin a) (Fin (m + l)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hkl : k ≤ l)
    (hs : 2 * l + 2 ≤ s) {T δ q : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hq : 0 < q)
    (hgap : sp.value (⟨m - 1, by omega⟩ : Fin (m + l)) ≤ T / 2)
    (hhead : ∀ j : Fin k, T ≤ sp.value (lastColumnIndex (m + l) k (by omega) j))
    (hn : chebyshevFilterDegree 1 (confidentRitzTolerance (2 * δ) q s (m + l)) < n) :
    (iidMatrixLaw a s 1) (krylovTailRitzEvent A sp k s n (by omega) (2 * δ) T)ᶜ ≤
      ENNReal.ofReal ((k : ℝ) * (2 / q)) := by
  let iTail : Fin (m + l) := ⟨m - 1, by omega⟩
  have hlow (i : Fin m) : sp.value (i.castAdd l) ≤ sp.value iTail := by
    apply sp.increasing
    change i.val ≤ m - 1
    omega
  by_cases hzero : sp.value iTail = 0
  · have hz (i : Fin m) : sp.value (i.castAdd l) = 0 :=
      le_antisymm ((hlow i).trans_eq hzero) (sp.value_nonneg (rightGram_posSemidef A) _)
    have hgood : ∀ᵐ U ∂iidMatrixLaw a s 1,
        U ∈ krylovTailRitzEvent A sp k s n (by omega) (2 * δ) T := by
      filter_upwards [krylov_gaussian_exact_of_zero_tail A sp hz (by omega : l ≤ s)
        ((Nat.zero_le _).trans_lt hn)] with U hU
      intro j
      change sp.value (lastColumnIndex (m + l) k (by omega) j) - ((2 * δ) / 2) * T ≤
        (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
          columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
            (lastColumnIndex (m + l) k (by omega) j)
      rw [hU, (canonicalOrderedSpectrum (m + l) (symmetricRightGram A)).value_unique sp]
      exact sub_le_self _ (by positivity)
    have hb : (iidMatrixLaw a s 1) (krylovTailRitzEvent A sp k s n (by omega) (2 * δ) T)ᶜ = 0 :=
      ae_iff.mp hgood
    rw [hb]
    exact zero_le _
  · have hL : 0 < sp.value iTail := lt_of_le_of_ne
      (sp.value_nonneg (rightGram_posSemidef A) _) (Ne.symm hzero)
    apply krylov_wide_gap_ritz_confidence_le A sp hkl _ hs hL (by dsimp [iTail] at hL ⊢; linarith)
      hδ hq hlow _ hn
    · intro j
      apply hL.trans_le (sp.increasing _)
      change m - 1 ≤ m + j.val
      omega
    · intro j
      have h := hhead j
      change sp.value iTail * (1 + (1 : ℝ) / 2) ≤ _
      change sp.value iTail ≤ T / 2 at hgap
      nlinarith

end
end LowRank
