import LowRank.WideGapRitz
import LowRank.TailEnergyGap
import LowRank.LargeTailKrylov

/-! A constant spectral gap below a wider head block gives relative
Schatten accuracy for the actual rank-k output, for 1 <= p <= 2. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

theorem refinedKrylovAlgorithm_wide_gap_success {b m l k s n : ℕ}
    (hm : 0 < m) (hk0 : 0 < k) (hkl : k ≤ l) (hkb : k ≤ b)
    (A : Matrix (Fin (m + l)) (Fin b) ℝ) (hs : 2 * l + 2 ≤ s)
    {p ε : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε)
    (hn : chebyshevFilterDegree 1
      (confidentRitzTolerance (ε / (k : ℝ)) (40 * (k : ℝ)) s (m + l)) < n)
    (hgap : (canonicalOrderedSpectrum (m + l) (symmetricRightGram Aᵀ)).value
      (⟨m - 1, by omega⟩ : Fin (m + l)) ≤
        (canonicalOrderedSpectrum (m + l) (symmetricRightGram Aᵀ)).value
          (⟨m + l - k - 1, by omega⟩ : Fin (m + l)) / 2) :
    19 / 20 ≤ (refinedKrylovAlgorithm.{u} (m + l) b k s n (by omega) hkb).law.real
      (rectangularSchattenSuccess p ε
        (refinedKrylovAlgorithm.{u} (m + l) b k s n (by omega) hkb).policy A) := by
  rw [refinedKrylovAlgorithm_success_probability (by omega) hkb (by linarith : 0 < p)]
  let sp := canonicalOrderedSpectrum (m + l) (symmetricRightGram Aᵀ)
  let iTail : Fin (m + l) := ⟨m + l - k - 1, by omega⟩
  let T := sp.value iTail
  have hT : 0 ≤ T := sp.value_nonneg (rightGram_posSemidef Aᵀ) _
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hhead (j : Fin k) : T ≤ sp.value (lastColumnIndex (m + l) k (by omega) j) := by
    apply sp.increasing
    change m + l - k - 1 ≤ m + l - k + j.val
    omega
  have htwo : 2 * (ε / (2 * (k : ℝ))) = ε / (k : ℝ) := by field_simp; ring
  have hb := krylov_wide_tail_gap_confidence_le hm Aᵀ sp hkl hs hT
    (div_pos hε (by positivity : 0 < 2 * (k : ℝ)))
    (by positivity : 0 < 40 * (k : ℝ)) hgap hhead (by simpa only [htwo] using hn)
  rw [htwo] at hb
  have he : (k : ℝ) * (2 / (40 * (k : ℝ))) = 1 / 20 := by field_simp; ring
  rw [he, ENNReal.ofReal_div_of_pos (by norm_num)] at hb
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at hb
  have hTpow : T ^ (p / 2) ≤ optimalSchattenPower p A k := by
    have h := optimalSchattenPower_ge_tail_count (k := k) (t := 1) Aᵀ sp (by omega) iTail
      (by change m + l - k - 1 + 1 ≤ m + l - k; omega) (by linarith : 0 < p)
    rw [optimalSchattenPower_transpose (by omega) hkb A (by linarith : 0 < p)] at h
    simpa only [Nat.cast_one, one_mul] using h
  have hbudget : (k : ℝ) * ((ε / (k : ℝ)) / 2) * T ^ (p / 2) ≤ ε * optimalSchattenPower p A k := by
    have hc : (k : ℝ) * ((ε / (k : ℝ)) / 2) = ε / 2 := by field_simp; ring
    rw [hc]
    exact (mul_le_mul_of_nonneg_right (by linarith : ε / 2 ≤ ε) (Real.rpow_nonneg hT _)).trans
      (mul_le_mul_of_nonneg_left hTpow hε.le)
  have hbad : (iidMatrixLaw b s 1)
      (rectangularSchattenSuccess p ε (refinedKrylovPolicy (m + l) b k s n (by omega) hkb) A)ᶜ ≤ 1 / 20 := by
    refine (measure_mono ?_).trans hb
    intro U hfail hU
    apply hfail
    have hpower := refinedKrylovPolicy_power_of_tail_ritz (by omega) hkb A U hp hp2
      (div_nonneg hε.le hkR.le) hT hhead hU
    apply schattenNorm_relative_of_power_excess hkb A _ hp hε.le
    dsimp only at hpower
    linarith
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 20 : ℝ≥0∞) ≠ ∞) hbad
  change (iidMatrixLaw b s 1).real _ ≤ _ at hr
  rw [measureReal_compl (measurableSet_rectangularSchattenSuccess hkb (by linarith : 0 < p) ε _ A),
    measureReal_univ_eq_one] at hr
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  linarith

theorem refinedKrylovAlgorithm_small_tail_success {b m l k s n : ℕ}
    (hm : 0 < m) (hk0 : 0 < k) (hkl : k ≤ l) (hkb : k ≤ b)
    (A : Matrix (Fin (m + l)) (Fin b) ℝ) (hs : 2 * l + 2 ≤ s)
    {p ε : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε)
    (hn : chebyshevFilterDegree 1
      (confidentRitzTolerance (ε / (k : ℝ)) (40 * (k : ℝ)) s (m + l)) < n)
    (hwide : 4 * ((k : ℝ) * accuracyScale ε) ≤ ((l - k : ℕ) : ℝ))
    (hsmall : optimalSchattenPower p A k < (k : ℝ) * accuracyScale ε *
      ((canonicalOrderedSpectrum (m + l) (symmetricRightGram Aᵀ)).value
        (⟨m + l - k - 1, by omega⟩ : Fin (m + l))) ^ (p / 2)) :
    19 / 20 ≤ (refinedKrylovAlgorithm.{u} (m + l) b k s n (by omega) hkb).law.real
      (rectangularSchattenSuccess p ε
        (refinedKrylovAlgorithm.{u} (m + l) b k s n (by omega) hkb).policy A) := by
  apply refinedKrylovAlgorithm_wide_gap_success hm hk0 hkl hkb A hs hp hp2 hε hn
  let sp := canonicalOrderedSpectrum (m + l) (symmetricRightGram Aᵀ)
  have hT := sp.value_nonneg (rightGram_posSemidef Aᵀ) (⟨m + l - k - 1, by omega⟩ : Fin (m + l))
  have hsmallT : optimalSchattenPower p Aᵀ k < (k : ℝ) * accuracyScale ε *
      sp.value (⟨m + l - k - 1, by omega⟩ : Fin (m + l)) ^ (p / 2) := by
    rw [optimalSchattenPower_transpose (by omega) hkb A (by linarith : 0 < p)]
    exact hsmall
  have h := spectral_cutoff_le_quarter_of_small_tail (k := k) (t := l - k) Aᵀ sp (by omega)
    (⟨m - 1, by omega⟩ : Fin (m + l)) (by change m - 1 + (l - k) ≤ m + l - k; omega)
    (by linarith : 0 < p) hp2
    (mul_pos (by exact_mod_cast hk0) (accuracyScale_pos hε)) hT hwide hsmallT
  linarith

theorem refinedKrylovAlgorithm_wide_query_count {a b k s : ℕ}
    (hk0 : 0 < k) (hka : k ≤ a) (hkb : k ≤ b) (hs : 0 < s)
    (A : Matrix (Fin a) (Fin b) ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let η := confidentRitzTolerance (ε / (k : ℝ)) (40 * (k : ℝ)) s a
    let n := chebyshevFilterDegree 1 η + 1
    ∀ seed : (refinedKrylovAlgorithm.{u} a b k s n hka hkb).Seed,
      (((refinedKrylovAlgorithm.{u} a b k s n hka hkb).policy.toProgram a b
        (krylovQueryBudget s 0 n) seed).calls (rectangularOracle A) : ℝ) ≤
          2 * (s : ℝ) * (2 * Real.log (2 / η) + 2) := by
  dsimp only
  intro seed
  rw [refinedKrylovAlgorithm_calls]
  push_cast
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hkpos : 0 < (k : ℝ) := by linarith
  have hη := confidentRitzTolerance_pos (d := a) (div_pos hε hkpos)
    (by positivity : 0 < 40 * (k : ℝ)) hs
  have hη1 := confidentRitzTolerance_le_one (d := a)
    ((div_le_one hkpos).mpr (hε1.trans hkR)) (by linarith : 1 ≤ 40 * (k : ℝ)) hs
  have h := chebyshevFilterDegree_le (by norm_num : (0 : ℝ) < 1) hη hη1
  norm_num only [Real.sqrt_one, div_one] at h
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * (s : ℝ))
  linarith

end
end LowRank
