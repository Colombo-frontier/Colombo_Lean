import LowRank.PowerBoostedRitzIndex
import LowRank.UnconditionalTailRitz

/-! All top-k power-weighted Ritz errors share one Gaussian Krylov run.
Zero tail spectra are handled by exact positive-support recovery. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators ENNReal
noncomputable section

def krylovPowerWeightedRitzEvent {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (k s n u : ℕ) (hk : k ≤ b) (δ L : ℝ) :
    Set (Matrix (Fin a) (Fin s) ℝ) :=
  {U | ∀ j : Fin k,
    let x := sp.value (lastColumnIndex b k hk j)
    x - (δ / 2) * L * (L / x) ^ (2 * u) ≤
      (canonicalOrderedSpectrum b (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value (lastColumnIndex b k hk j)}

theorem measurableSet_krylovPowerWeightedRitzEvent {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (k s n u : ℕ) (hk : k ≤ b) (δ L : ℝ) :
    MeasurableSet (krylovPowerWeightedRitzEvent A sp k s n u hk δ L) := by
  have he : krylovPowerWeightedRitzEvent A sp k s n u hk δ L =
      ⋂ j : Fin k, {U |
        sp.value (lastColumnIndex b k hk j) - (δ / 2) * L *
          (L / sp.value (lastColumnIndex b k hk j)) ^ (2 * u) ≤
        (canonicalOrderedSpectrum b (symmetricRightGram (A *
          columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value (lastColumnIndex b k hk j)} := by
    ext U
    simp only [krylovPowerWeightedRitzEvent, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun j => measurableSet_le measurable_const (measurable_krylovRitzValue A _))

theorem krylov_power_weighted_ritz_confidence_le {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hp : ∀ j : Fin k, 0 < sp.value (j.natAdd m)) (hs : 2 * k + 2 ≤ s)
    (u : ℕ) {L δ q : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hq : 0 < q)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ L) (hh : ∀ j : Fin k, L ≤ sp.value (j.natAdd m))
    (hn : chebyshevFilterDegree (powerBoostedGap δ u) (confidentRitzTolerance δ q s (m + k)) + u < n) :
    (iidMatrixLaw a s 1) (krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ L)ᶜ ≤
      ENNReal.ofReal ((k : ℝ) * (2 / q)) := by
  let E : Fin k → Set (Matrix (Fin a) (Fin s) ℝ) := fun j => {U |
    (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value (j.natAdd m) <
        sp.value (j.natAdd m) - (δ / 2) * L * (L / sp.value (j.natAdd m)) ^ (2 * u)}
  have he : (krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ L)ᶜ = ⋃ j : Fin k, E j := by
    ext U
    simp only [krylovPowerWeightedRitzEvent, E, lastColumnIndex_add, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_iUnion, not_forall, not_le]
  have hE (j : Fin k) : (iidMatrixLaw a s 1) (E j) ≤ ENNReal.ofReal (2 / q) :=
    krylov_gaussian_power_boosted_ritz_index_confidence_le A sp hp hs j u hL hδ hδ1 hq hl (hh j) hn
  rw [he]
  calc
    _ ≤ ∑ j : Fin k, (iidMatrixLaw a s 1) (E j) := by
      simpa only [tsum_fintype] using measure_iUnion_le E
    _ ≤ ∑ _ : Fin k, ENNReal.ofReal (2 / q) := Finset.sum_le_sum (fun j _ => hE j)
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun (_ : Fin k) _ => by positivity :
        ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ (2 : ℝ) / q)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem krylov_power_weighted_ritz_unconditional_confidence_le {a m k s n : ℕ} (hm : 0 < m)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * k + 2 ≤ s) (u : ℕ) {δ q : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hq : 0 < q)
    (hn : chebyshevFilterDegree (powerBoostedGap δ u) (confidentRitzTolerance δ q s (m + k)) + u < n) :
    (iidMatrixLaw a s 1) (krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ
      (sp.value (⟨m - 1, by omega⟩ : Fin (m + k))))ᶜ ≤ ENNReal.ofReal ((k : ℝ) * (2 / q)) := by
  let iTail : Fin (m + k) := ⟨m - 1, by omega⟩
  have hl (i : Fin m) : sp.value (i.castAdd k) ≤ sp.value iTail := by
    apply sp.increasing
    change i.val ≤ m - 1
    omega
  have hh (j : Fin k) : sp.value iTail ≤ sp.value (j.natAdd m) := by
    apply sp.increasing
    change m - 1 ≤ m + j.val
    omega
  by_cases hzero : sp.value iTail = 0
  · have hz (i : Fin m) : sp.value (i.castAdd k) = 0 :=
      le_antisymm ((hl i).trans_eq hzero) (sp.value_nonneg (rightGram_posSemidef A) _)
    have hgood : ∀ᵐ U ∂iidMatrixLaw a s 1, U ∈ krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ 0 := by
      filter_upwards [krylov_gaussian_exact_of_zero_tail A sp hz (by omega : k ≤ s) (by omega : 0 < n)] with U hU
      intro j
      change sp.value (lastColumnIndex (m + k) k (by omega) j) - (δ / 2) * 0 * _ ≤
        (canonicalOrderedSpectrum (m + k) (symmetricRightGram (A *
          columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
            (lastColumnIndex (m + k) k (by omega) j)
      rw [hU]
      simp only [mul_zero, zero_mul, sub_zero,
        (canonicalOrderedSpectrum (m + k) (symmetricRightGram A)).value_unique sp, le_refl]
    change (iidMatrixLaw a s 1) (krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ (sp.value iTail))ᶜ ≤ _
    have hb : (iidMatrixLaw a s 1) (krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ 0)ᶜ = 0 :=
      ae_iff.mp hgood
    rw [hzero, hb]
    exact zero_le _
  · have hL : 0 < sp.value iTail := lt_of_le_of_ne
      (sp.value_nonneg (rightGram_posSemidef A) _) (Ne.symm hzero)
    exact krylov_power_weighted_ritz_confidence_le A sp (fun j => hL.trans_le (hh j)) hs u
      hL hδ hδ1 hq hl hh hn

theorem krylov_power_weighted_ritz_unconditional_bad_le {a m k s n : ℕ} (hm : 0 < m) (hk : 0 < k)
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : 2 * k + 2 ≤ s) (u : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : chebyshevFilterDegree (powerBoostedGap δ u)
      (confidentRitzTolerance δ (40 * (k : ℝ)) s (m + k)) + u < n) :
    (iidMatrixLaw a s 1) (krylovPowerWeightedRitzEvent A sp k s n u (by omega) δ
      (sp.value (⟨m - 1, by omega⟩ : Fin (m + k))))ᶜ ≤ 1 / 20 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have h := krylov_power_weighted_ritz_unconditional_confidence_le hm A sp hs u hδ hδ1
    (by positivity : 0 < 40 * (k : ℝ)) hn
  have he : (k : ℝ) * (2 / (40 * (k : ℝ))) = 1 / 20 := by field_simp; ring
  rw [he, ENNReal.ofReal_div_of_pos (by norm_num)] at h
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at h
  exact h

end
end LowRank
