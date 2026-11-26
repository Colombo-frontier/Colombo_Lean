import LowRank.PairedKrylovConfidence
import LowRank.KrylovTailDimension
import LowRank.WideKrylovDimensions

/-! A single paired Krylov algorithm works for every input when 1 <= p <= 2
and the wide head fits the ambient dimension. Both query schedules depend
only on dimensions and accuracy; the energy split occurs only in the proof. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

theorem refinedPairedKrylovAlgorithm_all_input_success {a b k l s t n r : ℕ}
    (hk0 : 0 < k) (hkl : k ≤ l) (hl : l < a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (hs : 2 * k + 2 ≤ s) (ht : 2 * l + 2 ≤ t)
    {p ε : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : chebyshevFilterDegree (cubicKrylovGap ε)
      (confidentRitzTolerance (cubicKrylovGap ε) (40 * (k : ℝ)) s a) < n)
    (hr : chebyshevFilterDegree 1
      (confidentRitzTolerance (ε / (k : ℝ)) (40 * (k : ℝ)) t a) < r)
    (hwide : 4 * ((k : ℝ) * accuracyScale ε) ≤ ((l - k : ℕ) : ℝ)) :
    19 / 20 ≤ (refinedPairedKrylovAlgorithm.{u} a b k s t n r (by omega) hkb).law.real
      (rectangularSchattenSuccess p ε
        (refinedPairedKrylovAlgorithm.{u} a b k s t n r (by omega) hkb).policy A) := by
  apply refinedPairedKrylovAlgorithm_success_of_bad_le (by omega) hkb A (by linarith : 0 < p)
  let sp := canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)
  let iTail : Fin a := ⟨a - k - 1, by omega⟩
  let T := sp.value iTail
  have hT : 0 ≤ T := sp.value_nonneg (rightGram_posSemidef Aᵀ) _
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hhead (j : Fin k) : T ≤ sp.value (lastColumnIndex a k (by omega) j) := by
    apply sp.increasing
    change a - k - 1 ≤ a - k + j.val
    omega
  by_cases hlarge : (k : ℝ) * accuracyScale ε * T ^ (p / 2) ≤ optimalSchattenPower p A k
  · have hbudget : (k : ℝ) * (cubicKrylovGap ε / 2) * T ^ (p / 2) ≤
        ε * optimalSchattenPower p A k := by
      calc
        _ ≤ (k : ℝ) * cubicKrylovGap ε * T ^ (p / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (by linarith [cubicKrylovGap_pos hε] : cubicKrylovGap ε / 2 ≤ cubicKrylovGap ε)
            (Nat.cast_nonneg k)) (Real.rpow_nonneg hT _)
        _ = ε * ((k : ℝ) * accuracyScale ε * T ^ (p / 2)) := by
          rw [cubicKrylovGap_eq_mul_scale hε]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlarge hε.le
    apply refinedPairedKrylovPolicy_bad_of_left_tail_ritz (by omega) hkb A hp hp2 hε.le
      (cubicKrylovGap_pos hε).le hT hhead hbudget
    exact krylov_tail_ritz_bad_le_dim (by omega) hk0 Aᵀ sp hs
      (cubicKrylovGap_pos hε) (cubicKrylovGap_le_one hε.le hε1) hn
  · have hsmall : optimalSchattenPower p Aᵀ k < (k : ℝ) * accuracyScale ε * T ^ (p / 2) := by
      rw [optimalSchattenPower_transpose (by omega) hkb A (by linarith : 0 < p)]
      exact lt_of_not_ge hlarge
    have hcut := spectral_cutoff_le_quarter_of_small_tail (k := k) (t := l - k) Aᵀ sp (by omega)
      (⟨a - l - 1, by omega⟩ : Fin a) (by change a - l - 1 + (l - k) ≤ a - k; omega)
      (by linarith : 0 < p) hp2 (mul_pos hkR (accuracyScale_pos hε)) hT hwide hsmall
    have hTpow : T ^ (p / 2) ≤ optimalSchattenPower p A k := by
      have h := optimalSchattenPower_ge_tail_count (k := k) (t := 1) Aᵀ sp (by omega) iTail
        (by change a - k - 1 + 1 ≤ a - k; omega) (by linarith : 0 < p)
      rw [optimalSchattenPower_transpose (by omega) hkb A (by linarith : 0 < p)] at h
      simpa only [Nat.cast_one, one_mul] using h
    have hbudget : (k : ℝ) * ((ε / (k : ℝ)) / 2) * T ^ (p / 2) ≤ ε * optimalSchattenPower p A k := by
      have hc : (k : ℝ) * ((ε / (k : ℝ)) / 2) = ε / 2 := by field_simp; ring
      rw [hc]
      exact (mul_le_mul_of_nonneg_right (by linarith : ε / 2 ≤ ε) (Real.rpow_nonneg hT _)).trans
        (mul_le_mul_of_nonneg_left hTpow hε.le)
    apply refinedPairedKrylovPolicy_bad_of_right_tail_ritz (by omega) hkb A hp hp2 hε.le
      (div_nonneg hε.le hkR.le) hT hhead hbudget
    exact krylov_wide_tail_gap_bad_le_dim hl hk0 hkl Aᵀ sp ht hT (div_pos hε hkR)
      (by linarith : sp.value (⟨a - l - 1, by omega⟩ : Fin a) ≤ T / 2) hhead hr

theorem refinedPairedKrylovAlgorithm_cubic_success {a b k : ℕ}
    (hk0 : 0 < k) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    {p ε : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfit : wideKrylovRank k ε < a) :
    let s := 2 * k + 2
    let t := 2 * wideKrylovRank k ε + 2
    let n := chebyshevFilterDegree (cubicKrylovGap ε)
      (confidentRitzTolerance (cubicKrylovGap ε) (40 * (k : ℝ)) s a) + 1
    let r := chebyshevFilterDegree 1 (confidentRitzTolerance (ε / (k : ℝ)) (40 * (k : ℝ)) t a) + 1
    let hka : k ≤ a := (wideKrylovRank_ge k ε).trans hfit.le
    19 / 20 ≤ (refinedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).law.real
      (rectangularSchattenSuccess p ε (refinedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).policy A) := by
  dsimp only
  exact refinedPairedKrylovAlgorithm_all_input_success hk0 (wideKrylovRank_ge k ε) hfit hkb A
    (le_refl _) (le_refl _) hp hp2 hε hε1 (Nat.lt_succ_self _) (Nat.lt_succ_self _)
    (wideKrylovRank_surplus k ε)

end
end LowRank
