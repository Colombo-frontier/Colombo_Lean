import LowRank.WidePowerBoostedRitzIndex
import LowRank.SimultaneousPowerWeightedRitz
import LowRank.WideGapRitz

/-! Simultaneous weighted accuracy from a wide Krylov block, including
zero cutoffs and rank-deficient inputs. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators ENNReal
noncomputable section

theorem krylov_wide_power_weighted_confidence_le {a m l k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + l)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hkl : k ≤ l)
    (hp : ∀ j : Fin l, 0 < sp.value (j.natAdd m)) (hs : 2 * l + 2 ≤ s)
    (u : ℕ) {c T δ q : ℝ} (hc : 0 < c) (hcT : c ≤ T) (hδ : 0 < δ) (hq : 0 < q)
    (hl : ∀ i : Fin m, sp.value (i.castAdd l) ≤ c)
    (hhead : ∀ j : Fin k, T ≤ sp.value (lastColumnIndex (m + l) k (by omega) j))
    (hgap : ∀ j : Fin k, c * (1 + (1 : ℝ) / 2) ≤ sp.value (lastColumnIndex (m + l) k (by omega) j))
    (hn : chebyshevFilterDegree 1 (confidentRitzTolerance δ q s (m + l)) + u < n) :
    (iidMatrixLaw a s 1) (krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ T)ᶜ ≤
      ENNReal.ofReal ((k : ℝ) * (2 / q)) := by
  let E : Fin k → Set (Matrix (Fin a) (Fin s) ℝ) := fun j => {U |
    (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
        (lastColumnIndex (m + l) k (by omega) j) <
          sp.value (lastColumnIndex (m + l) k (by omega) j) - (δ / 2) * T *
            (T / sp.value (lastColumnIndex (m + l) k (by omega) j)) ^ (2 * u)}
  have he : (krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ T)ᶜ = ⋃ j : Fin k, E j := by
    ext U
    simp only [krylovPowerWeightedRitzEvent, E, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_iUnion, not_forall, not_le]
  have hE (j : Fin k) : (iidMatrixLaw a s 1) (E j) ≤ ENNReal.ofReal (2 / q) := by
    have hi := lastColumnIndex_natAdd m l k hkl (by omega) j
    have h := krylov_gaussian_wide_power_boosted_index_confidence_le A sp hp hs
      (lastColumnIndex l k hkl j) u hc hcT hδ hq hl
      (by simpa only [hi] using hhead j) (by simpa only [hi] using hgap j) hn
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

theorem krylov_wide_power_weighted_unconditional_confidence_le {a m l k s n : ℕ} (hm : 0 < m)
    (A : Matrix (Fin a) (Fin (m + l)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hkl : k ≤ l)
    (hs : 2 * l + 2 ≤ s) (u : ℕ) {T δ q : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hq : 0 < q)
    (hgap : sp.value (⟨m - 1, by omega⟩ : Fin (m + l)) ≤ T / 2)
    (hhead : ∀ j : Fin k, T ≤ sp.value (lastColumnIndex (m + l) k (by omega) j))
    (hn : chebyshevFilterDegree 1 (confidentRitzTolerance δ q s (m + l)) + u < n) :
    (iidMatrixLaw a s 1) (krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ T)ᶜ ≤
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
        U ∈ krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ T := by
      filter_upwards [krylov_gaussian_exact_of_zero_tail A sp hz (by omega : l ≤ s)
        (by omega : 0 < n)] with U hU
      intro j
      change sp.value (lastColumnIndex (m + l) k (by omega) j) - (δ / 2) * T *
          (T / sp.value (lastColumnIndex (m + l) k (by omega) j)) ^ (2 * u) ≤
        (canonicalOrderedSpectrum (m + l) (symmetricRightGram (A *
          columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
            (lastColumnIndex (m + l) k (by omega) j)
      rw [hU, (canonicalOrderedSpectrum (m + l) (symmetricRightGram A)).value_unique sp]
      have hx := sp.value_nonneg (rightGram_posSemidef A) (lastColumnIndex (m + l) k (by omega) j)
      exact sub_le_self _ (by positivity)
    have hb : (iidMatrixLaw a s 1) (krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ T)ᶜ = 0 :=
      ae_iff.mp hgood
    rw [hb]
    exact zero_le _
  · have hc : 0 < sp.value iTail := lt_of_le_of_ne
      (sp.value_nonneg (rightGram_posSemidef A) _) (Ne.symm hzero)
    apply krylov_wide_power_weighted_confidence_le A sp hkl _ hs u hc
      (by dsimp [iTail] at hc ⊢; linarith) hδ hq hlow hhead _ hn
    · intro j
      apply hc.trans_le (sp.increasing _)
      change m - 1 ≤ m + j.val
      omega
    · intro j
      have h := hhead j
      change sp.value iTail * (1 + (1 : ℝ) / 2) ≤ _
      change sp.value iTail ≤ T / 2 at hgap
      nlinarith

end
end LowRank
