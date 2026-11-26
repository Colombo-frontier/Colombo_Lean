import LowRank.SimultaneousKrylovRitz
import LowRank.RefinedKrylovGuarantees

/-! Simultaneous relative Ritz accuracy controls the actual refined output
for every p >= 1. The additive power error is proportional to captured
head energy; a separate explicit budget is needed for relative tail error. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators ENNReal
noncomputable section
universe u

theorem relative_div_lower {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    x - h * x ≤ x / (1 + h) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 + h)).mpr
  nlinarith [mul_nonneg (sq_nonneg h) hx]

theorem mul_rpow_sub_one_of_nonneg {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r) :
    x * x ^ (r - 1) = x ^ r := by
  rcases eq_or_lt_of_le hx with hx | hx
  · rw [← hx, zero_mul, Real.zero_rpow (ne_of_gt hr)]
  · rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp

theorem optimalColumnSelector_relative_power_deficit {a b c k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (M : Matrix (Fin c) (Fin b) ℝ)
    {p γ : ℝ} (hp : 0 < p) (hγ : 0 ≤ γ)
    (happrox : ∀ j : Fin k,
      (canonicalOrderedSpectrum b (symmetricRightGram A)).value (lastColumnIndex b k hk j) / (1 + γ / 2) ≤
        (canonicalOrderedSpectrum b (symmetricRightGram M)).value (lastColumnIndex b k hk j)) :
    schattenPower p (A * optimalColumnSelector a b k hk A) -
      (max 1 (p / 2) * (γ / 2)) * schattenPower p (A * optimalColumnSelector a b k hk A) ≤
        schattenPower p (M * optimalColumnSelector c b k hk M) := by
  let x := fun j : Fin k => (canonicalOrderedSpectrum b (symmetricRightGram A)).value (lastColumnIndex b k hk j)
  have hx (j : Fin k) : 0 ≤ x j :=
    (canonicalOrderedSpectrum b (symmetricRightGram A)).value_nonneg (rightGram_posSemidef A) _
  have h := optimalColumnSelector_power_deficit hk M hp x (fun j => (γ / 2) * x j) hx
    (fun j => mul_nonneg (by positivity) (hx j))
    (fun j => (relative_div_lower (hx j) (by positivity : 0 ≤ γ / 2)).trans (happrox j))
  have he : (∑ j, max 1 (p / 2) * ((γ / 2) * x j) * x j ^ (p / 2 - 1)) =
      (max 1 (p / 2) * (γ / 2)) * ∑ j, x j ^ (p / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [mul_assoc, mul_rpow_sub_one_of_nonneg (hx j) (by positivity : 0 < p / 2)]
  rw [he] at h
  simpa only [optimalColumnSelector_schattenPower, x] using h

theorem refinedKrylovPolicy_power_of_relative_ritz {a b k s n : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin b) (Fin s) ℝ) {p γ : ℝ} (hp : 1 ≤ p) (hγ : 0 ≤ γ)
    (hU : U ∈ krylovRelativeRitzEvent Aᵀ (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k s n hka γ) :
    let Z := runBoundedRectangular a b (krylovQueryBudget s 0 n)
      (refinedKrylovPolicy a b k s n hka hkb) A U
    schattenPower p (A * (1 - Z * Zᵀ)) ≤ optimalSchattenPower p A k +
      (max 1 (p / 2) * (γ / 2)) * schattenPower p (Aᵀ * optimalColumnSelector b a k hka Aᵀ) := by
  have hc := optimalColumnSelector_relative_power_deficit hka Aᵀ
    (Aᵀ * columnRangeProjector (krylovRightBlocks (krylovBlockData Aᵀ n U)))
    (by linarith : 0 < p) hγ hU
  dsimp only
  rw [refinedKrylovPolicy_run]
  exact refinedRitzColumns_residual_le_optimum_add_deficit hka hkb A
    (columnRangeProjector_isProjector _) hp hc

theorem refinedKrylovPolicy_gap_free_power_bad_le {a b k s n : ℕ} (hk0 : 0 < k)
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (hs : 2 * k + 2 ≤ s) {p γ : ℝ} (hp : 1 ≤ p) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s a) < n) :
    (iidMatrixLaw b s 1) {U |
      let Z := runBoundedRectangular a b (krylovQueryBudget s 0 n)
        (refinedKrylovPolicy a b k s n hka hkb) A U
      optimalSchattenPower p A k + (max 1 (p / 2) * (γ / 2)) *
        schattenPower p (Aᵀ * optimalColumnSelector b a k hka Aᵀ) <
          schattenPower p (A * (1 - Z * Zᵀ))} ≤ 1 / 20 := by
  refine (measure_mono ?_).trans (krylov_simultaneous_relative_ritz_bad_le hk0 Aᵀ
    (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) hka hs hγ hγ1 hn)
  intro U hbad hU
  exact (not_lt_of_ge (refinedKrylovPolicy_power_of_relative_ritz hka hkb A U hp hγ.le hU)) hbad

theorem refinedKrylovPolicy_relative_success_of_head_budget {a b k s n : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin b) (Fin s) ℝ) {p γ ε : ℝ} (hp : 1 ≤ p) (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hU : U ∈ krylovRelativeRitzEvent Aᵀ (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k s n hka γ)
    (hbudget : (max 1 (p / 2) * (γ / 2)) * schattenPower p (Aᵀ * optimalColumnSelector b a k hka Aᵀ) ≤
      ε * optimalSchattenPower p A k) :
    U ∈ rectangularSchattenSuccess p ε (refinedKrylovPolicy a b k s n hka hkb) A := by
  have h := refinedKrylovPolicy_power_of_relative_ritz hka hkb A U hp hγ hU
  dsimp only at h
  apply schattenNorm_relative_of_power_excess hkb A _ hp hε
  linarith

theorem refinedKrylovPolicy_gap_free_success_of_head_budget {a b k s n : ℕ} (hk0 : 0 < k)
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (hs : 2 * k + 2 ≤ s) {p γ ε : ℝ} (hp : 1 ≤ p) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 ≤ ε)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s a) < n)
    (hbudget : (max 1 (p / 2) * (γ / 2)) * schattenPower p (Aᵀ * optimalColumnSelector b a k hka Aᵀ) ≤
      ε * optimalSchattenPower p A k) :
    19 / 20 ≤ (iidMatrixLaw b s 1).real
      (rectangularSchattenSuccess p ε (refinedKrylovPolicy a b k s n hka hkb) A) := by
  have hbad : (iidMatrixLaw b s 1)
      (rectangularSchattenSuccess p ε (refinedKrylovPolicy a b k s n hka hkb) A)ᶜ ≤ 1 / 20 := by
    refine (measure_mono ?_).trans (krylov_simultaneous_relative_ritz_bad_le hk0 Aᵀ
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) hka hs hγ hγ1 hn)
    intro U hfail hU
    exact hfail (refinedKrylovPolicy_relative_success_of_head_budget hka hkb A U hp hγ.le hε hU hbudget)
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 20 : ℝ≥0∞) ≠ ∞) hbad
  change (iidMatrixLaw b s 1).real _ ≤ _ at hr
  rw [measureReal_compl (measurableSet_rectangularSchattenSuccess hkb (by linarith : 0 < p) ε _ A),
    measureReal_univ_eq_one] at hr
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  linarith

theorem refinedKrylovAlgorithm_gap_free_success_of_head_budget {a b k s n : ℕ} (hk0 : 0 < k)
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (hs : 2 * k + 2 ≤ s) {p γ ε : ℝ} (hp : 1 ≤ p) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 ≤ ε)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s a) < n)
    (hbudget : (max 1 (p / 2) * (γ / 2)) * schattenPower p (Aᵀ * optimalColumnSelector b a k hka Aᵀ) ≤
      ε * optimalSchattenPower p A k) :
    19 / 20 ≤ (refinedKrylovAlgorithm.{u} a b k s n hka hkb).law.real
      (rectangularSchattenSuccess p ε (refinedKrylovAlgorithm.{u} a b k s n hka hkb).policy A) := by
  rw [refinedKrylovAlgorithm_success_probability hka hkb (by linarith : 0 < p)]
  exact refinedKrylovPolicy_gap_free_success_of_head_budget hk0 hka hkb A hs hp hγ hγ1 hε hn hbudget

end
end LowRank
