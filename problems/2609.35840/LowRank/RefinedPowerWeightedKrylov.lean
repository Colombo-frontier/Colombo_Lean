import LowRank.SimultaneousPowerWeightedRitz
import LowRank.PowerWeightedTailBudget

/-! The weighted simultaneous Ritz event controls actual relative
Schatten residuals for every finite p >= 1, under an explicit tail budget. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

theorem refinedKrylovPolicy_power_of_weighted_tail_ritz {a b k s n : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin b) (Fin s) ℝ) (v : ℕ) {p δ L : ℝ} (hp : 1 ≤ p)
    (hv : p / 2 - 1 ≤ ((2 * v : ℕ) : ℝ)) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value (lastColumnIndex a k hka j))
    (hU : U ∈ krylovPowerWeightedRitzEvent Aᵀ (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k s n v hka δ L) :
    let Z := runBoundedRectangular a b (krylovQueryBudget s 0 n)
      (refinedKrylovPolicy a b k s n hka hkb) A U
    schattenPower p (A * (1 - Z * Zᵀ)) ≤ optimalSchattenPower p A k +
      max 1 (p / 2) * (k : ℝ) * (δ / 2) * L ^ (p / 2) := by
  have hc := optimalColumnSelector_power_weighted_tail_deficit hka Aᵀ
    (Aᵀ * columnRangeProjector (krylovRightBlocks (krylovBlockData Aᵀ n U))) v
    (by linarith : 0 < p) hv (by positivity : 0 ≤ δ / 2) hL hhead hU
  dsimp only
  rw [refinedKrylovPolicy_run]
  exact refinedRitzColumns_residual_le_optimum_add_deficit hka hkb A (columnRangeProjector_isProjector _) hp hc

theorem refinedKrylovAlgorithm_weighted_tail_success_of_budget {b m k s n : ℕ}
    (hm : 0 < m) (hk0 : 0 < k) (hkb : k ≤ b)
    (A : Matrix (Fin (m + k)) (Fin b) ℝ) (hs : 2 * k + 2 ≤ s)
    (v : ℕ) {p δ ε : ℝ} (hp : 1 ≤ p) (hv : p / 2 - 1 ≤ ((2 * v : ℕ) : ℝ))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hn : chebyshevFilterDegree (powerBoostedGap δ v)
      (confidentRitzTolerance δ (40 * (k : ℝ)) s (m + k)) + v < n)
    (hbudget : max 1 (p / 2) * (k : ℝ) * (δ / 2) *
      ((canonicalOrderedSpectrum (m + k) (symmetricRightGram Aᵀ)).value
        (⟨m - 1, by omega⟩ : Fin (m + k))) ^ (p / 2) ≤ ε * optimalSchattenPower p A k) :
    19 / 20 ≤ (refinedKrylovAlgorithm.{u} (m + k) b k s n (by omega) hkb).law.real
      (rectangularSchattenSuccess p ε
        (refinedKrylovAlgorithm.{u} (m + k) b k s n (by omega) hkb).policy A) := by
  rw [refinedKrylovAlgorithm_success_probability (by omega) hkb (by linarith : 0 < p)]
  let sp := canonicalOrderedSpectrum (m + k) (symmetricRightGram Aᵀ)
  have hhead (j : Fin k) : sp.value (⟨m - 1, by omega⟩ : Fin (m + k)) ≤
      sp.value (lastColumnIndex (m + k) k (by omega) j) := by
    apply sp.increasing
    simp only [lastColumnIndex_add]
    change m - 1 ≤ m + j.val
    omega
  have hbad : (iidMatrixLaw b s 1)
      (rectangularSchattenSuccess p ε (refinedKrylovPolicy (m + k) b k s n (by omega) hkb) A)ᶜ ≤ 1 / 20 := by
    refine (measure_mono ?_).trans (krylov_power_weighted_ritz_unconditional_bad_le hm hk0 Aᵀ sp hs v hδ hδ1 hn)
    intro U hfail hU
    apply hfail
    have hpower := refinedKrylovPolicy_power_of_weighted_tail_ritz (by omega) hkb A U v hp hv hδ.le
      (sp.value_nonneg (rightGram_posSemidef Aᵀ) _) hhead hU
    apply schattenNorm_relative_of_power_excess hkb A _ hp hε
    dsimp only at hpower
    linarith
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 20 : ℝ≥0∞) ≠ ∞) hbad
  change (iidMatrixLaw b s 1).real _ ≤ _ at hr
  rw [measureReal_compl (measurableSet_rectangularSchattenSuccess hkb (by linarith : 0 < p) ε _ A),
    measureReal_univ_eq_one] at hr
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  linarith

end
end LowRank
