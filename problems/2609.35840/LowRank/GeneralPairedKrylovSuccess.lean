import LowRank.PairedPowerWeightedKrylov
import LowRank.PowerWeightedRitzDimension
import LowRank.GeneralKrylovParameters

/-! The paired algorithm succeeds for every input and every finite p >= 1.
The energy split occurs only in the proof, with fixed query schedules. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

theorem refinedPairedKrylovAlgorithm_general_all_input_success {a b k l s t n r : ℕ}
    (hk0 : 0 < k) (hkl : k ≤ l) (hl : l < a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (hs : 2 * k + 2 ≤ s) (ht : 2 * l + 2 ≤ t)
    (v : ℕ) {p ε : ℝ} (hp : 1 ≤ p) (hv : p / 2 - 1 ≤ ((2 * v : ℕ) : ℝ))
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : chebyshevFilterDegree (powerBoostedGap (weightedNarrowError p ε) v)
      (confidentRitzTolerance (weightedNarrowError p ε) (40 * (k : ℝ)) s a) + v < n)
    (hr : chebyshevFilterDegree 1
      (confidentRitzTolerance (weightedWideError p k ε) (40 * (k : ℝ)) t a) + v < r)
    (hwide : (4 : ℝ) ^ (p / 2) * ((k : ℝ) * accuracyScale ε) ≤ ((l - k : ℕ) : ℝ)) :
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
  · apply refinedPairedKrylovPolicy_bad_of_left_weighted_ritz (by omega) hkb A v hp hv hε.le
      (weightedNarrowError_pos (p := p) hε).le hT hhead (weightedNarrowError_budget hε hT hlarge)
    exact krylov_power_weighted_bad_le_dim (by omega) hk0 Aᵀ sp hs v
      (weightedNarrowError_pos hε) (weightedNarrowError_le_one hε.le hε1) hn
  · have hsmall : optimalSchattenPower p Aᵀ k < (k : ℝ) * accuracyScale ε * T ^ (p / 2) := by
      rw [optimalSchattenPower_transpose (by omega) hkb A (by linarith : 0 < p)]
      exact lt_of_not_ge hlarge
    have hcut := spectral_cutoff_le_quarter_of_general_small_tail (k := k) (t := l - k) Aᵀ sp (by omega)
      (⟨a - l - 1, by omega⟩ : Fin a) (by change a - l - 1 + (l - k) ≤ a - k; omega)
      (by linarith : 0 < p) (mul_pos hkR (accuracyScale_pos hε)) hT hwide hsmall
    have hTpow : T ^ (p / 2) ≤ optimalSchattenPower p A k := by
      have h := optimalSchattenPower_ge_tail_count (k := k) (t := 1) Aᵀ sp (by omega) iTail
        (by change a - k - 1 + 1 ≤ a - k; omega) (by linarith : 0 < p)
      rw [optimalSchattenPower_transpose (by omega) hkb A (by linarith : 0 < p)] at h
      simpa only [Nat.cast_one, one_mul] using h
    apply refinedPairedKrylovPolicy_bad_of_right_weighted_ritz (by omega) hkb A v hp hv hε.le
      (weightedWideError_pos (p := p) hk0 hε).le hT hhead (weightedWideError_budget hk0 hε.le hT hTpow)
    exact krylov_wide_power_weighted_bad_le_dim hl hk0 hkl Aᵀ sp ht v hT (weightedWideError_pos hk0 hε)
      (by linarith : sp.value (⟨a - l - 1, by omega⟩ : Fin a) ≤ T / 2) hhead hr

theorem refinedPairedKrylovAlgorithm_general_success {a b k : ℕ}
    (hk0 : 0 < k) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfit : generalWideKrylovRank p k ε < a) :
    let s := 2 * k + 2
    let t := 2 * generalWideKrylovRank p k ε + 2
    let v := powerBoostOrder p
    let n := chebyshevFilterDegree (powerBoostedGap (weightedNarrowError p ε) v)
      (confidentRitzTolerance (weightedNarrowError p ε) (40 * (k : ℝ)) s a) + v + 1
    let r := chebyshevFilterDegree 1
      (confidentRitzTolerance (weightedWideError p k ε) (40 * (k : ℝ)) t a) + v + 1
    let hka : k ≤ a := (generalWideKrylovRank_ge p k ε).trans hfit.le
    19 / 20 ≤ (refinedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).law.real
      (rectangularSchattenSuccess p ε (refinedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).policy A) := by
  dsimp only
  exact refinedPairedKrylovAlgorithm_general_all_input_success hk0 (generalWideKrylovRank_ge p k ε)
    hfit hkb A (le_refl _) (le_refl _) (powerBoostOrder p) hp (powerBoostOrder_sufficient p)
    hε hε1 (Nat.lt_succ_self _) (Nat.lt_succ_self _) (generalWideKrylovRank_surplus p k ε)

end
end LowRank
