import LowRank.UnconditionalTailRitz
import LowRank.RefinedKrylovGapFreePower

/-! For 1 <= p <= 2, tail-scaled Ritz errors have a power loss controlled
by the tail cutoff alone. The resulting bound applies to the actual output. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators ENNReal
noncomputable section
universe u

theorem tail_scale_power_loss_le {k : ℕ} (x : Fin k → ℝ) {p γ L : ℝ}
    (hp : 0 < p) (hp2 : p ≤ 2) (hγ : 0 ≤ γ) (hL : 0 ≤ L) (hx : ∀ j, L ≤ x j) :
    (∑ j, max 1 (p / 2) * ((γ / 2) * L) * x j ^ (p / 2 - 1)) ≤
      (k : ℝ) * (γ / 2) * L ^ (p / 2) := by
  rw [max_eq_left (by linarith : p / 2 ≤ 1)]
  rcases eq_or_lt_of_le hL with hL | hL
  · simp only [← hL, mul_zero, zero_mul, Real.zero_rpow (by linarith : p / 2 ≠ 0), Finset.sum_const_zero]
    exact le_refl _
  · calc
      _ ≤ ∑ _ : Fin k, (γ / 2) * L ^ (p / 2) := by
        apply Finset.sum_le_sum
        intro j _
        have h := Real.rpow_le_rpow_of_nonpos hL (hx j) (by linarith : p / 2 - 1 ≤ 0)
        calc
          _ ≤ ((γ / 2) * L) * L ^ (p / 2 - 1) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (γ / 2) * L)
          _ = _ := by rw [mul_assoc, mul_rpow_sub_one_of_nonneg hL.le (by positivity : 0 < p / 2)]
      _ = _ := by simp [mul_assoc]

theorem optimalColumnSelector_tail_power_deficit {a b c k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (M : Matrix (Fin c) (Fin b) ℝ)
    {p γ L : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) (hγ : 0 ≤ γ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum b (symmetricRightGram A)).value (lastColumnIndex b k hk j))
    (happrox : ∀ j : Fin k,
      (canonicalOrderedSpectrum b (symmetricRightGram A)).value (lastColumnIndex b k hk j) - (γ / 2) * L ≤
        (canonicalOrderedSpectrum b (symmetricRightGram M)).value (lastColumnIndex b k hk j)) :
    schattenPower p (A * optimalColumnSelector a b k hk A) - (k : ℝ) * (γ / 2) * L ^ (p / 2) ≤
      schattenPower p (M * optimalColumnSelector c b k hk M) := by
  let x := fun j : Fin k => (canonicalOrderedSpectrum b (symmetricRightGram A)).value (lastColumnIndex b k hk j)
  have hx (j : Fin k) : 0 ≤ x j :=
    (canonicalOrderedSpectrum b (symmetricRightGram A)).value_nonneg (rightGram_posSemidef A) _
  have h := optimalColumnSelector_power_deficit hk M hp x (fun _ => (γ / 2) * L) hx
    (fun _ => by positivity) happrox
  have hb := tail_scale_power_loss_le x hp hp2 hγ hL hhead
  rw [← optimalColumnSelector_schattenPower hk A p] at h
  linarith

theorem refinedKrylovPolicy_power_of_tail_ritz {a b k s n : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin b) (Fin s) ℝ) {p γ L : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hγ : 0 ≤ γ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value (lastColumnIndex a k hka j))
    (hU : U ∈ krylovTailRitzEvent Aᵀ (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k s n hka γ L) :
    let Z := runBoundedRectangular a b (krylovQueryBudget s 0 n)
      (refinedKrylovPolicy a b k s n hka hkb) A U
    schattenPower p (A * (1 - Z * Zᵀ)) ≤ optimalSchattenPower p A k +
      (k : ℝ) * (γ / 2) * L ^ (p / 2) := by
  have hc := optimalColumnSelector_tail_power_deficit hka Aᵀ
    (Aᵀ * columnRangeProjector (krylovRightBlocks (krylovBlockData Aᵀ n U)))
    (by linarith : 0 < p) hp2 hγ hL hhead hU
  dsimp only
  rw [refinedKrylovPolicy_run]
  exact refinedRitzColumns_residual_le_optimum_add_deficit hka hkb A
    (columnRangeProjector_isProjector _) hp hc

theorem refinedKrylovPolicy_tail_power_bad_le {b m k s n : ℕ}
    (hm : 0 < m) (hk0 : 0 < k) (hkb : k ≤ b)
    (A : Matrix (Fin (m + k)) (Fin b) ℝ) (hs : 2 * k + 2 ≤ s)
    {p γ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s (m + k)) < n) :
    let L := (canonicalOrderedSpectrum (m + k) (symmetricRightGram Aᵀ)).value
      (⟨m - 1, by omega⟩ : Fin (m + k))
    (iidMatrixLaw b s 1) {U |
      let Z := runBoundedRectangular (m + k) b (krylovQueryBudget s 0 n)
        (refinedKrylovPolicy (m + k) b k s n (by omega) hkb) A U
      optimalSchattenPower p A k + (k : ℝ) * (γ / 2) * L ^ (p / 2) <
        schattenPower p (A * (1 - Z * Zᵀ))} ≤ 1 / 20 := by
  let sp := canonicalOrderedSpectrum (m + k) (symmetricRightGram Aᵀ)
  dsimp only
  refine (measure_mono ?_).trans
    (krylov_simultaneous_tail_ritz_unconditional_bad_le hm hk0 Aᵀ sp hs hγ hγ1 hn)
  intro U hbad hU
  have hhead (j : Fin k) : sp.value (⟨m - 1, by omega⟩ : Fin (m + k)) ≤
      sp.value (lastColumnIndex (m + k) k (by omega) j) := by
    apply sp.increasing
    simp only [lastColumnIndex_add]
    change m - 1 ≤ m + j.val
    omega
  exact (not_lt_of_ge (refinedKrylovPolicy_power_of_tail_ritz (by omega) hkb A U hp hp2 hγ.le
    (sp.value_nonneg (rightGram_posSemidef Aᵀ) _) hhead hU)) hbad

theorem refinedKrylovPolicy_tail_success_of_budget {b m k s n : ℕ}
    (hm : 0 < m) (hk0 : 0 < k) (hkb : k ≤ b)
    (A : Matrix (Fin (m + k)) (Fin b) ℝ) (hs : 2 * k + 2 ≤ s)
    {p γ ε : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 ≤ ε)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s (m + k)) < n)
    (hbudget : (k : ℝ) * (γ / 2) *
      ((canonicalOrderedSpectrum (m + k) (symmetricRightGram Aᵀ)).value
        (⟨m - 1, by omega⟩ : Fin (m + k))) ^ (p / 2) ≤ ε * optimalSchattenPower p A k) :
    19 / 20 ≤ (iidMatrixLaw b s 1).real
      (rectangularSchattenSuccess p ε (refinedKrylovPolicy (m + k) b k s n (by omega) hkb) A) := by
  have hbad : (iidMatrixLaw b s 1)
      (rectangularSchattenSuccess p ε (refinedKrylovPolicy (m + k) b k s n (by omega) hkb) A)ᶜ ≤ 1 / 20 := by
    refine (measure_mono ?_).trans (refinedKrylovPolicy_tail_power_bad_le hm hk0 hkb A hs hp hp2 hγ hγ1 hn)
    intro U hfail
    by_contra! hpower
    apply hfail
    apply schattenNorm_relative_of_power_excess hkb A _ hp hε
    simp only [Set.mem_setOf_eq, not_lt] at hpower
    linarith
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 20 : ℝ≥0∞) ≠ ∞) hbad
  change (iidMatrixLaw b s 1).real _ ≤ _ at hr
  rw [measureReal_compl (measurableSet_rectangularSchattenSuccess hkb (by linarith : 0 < p) ε _ A),
    measureReal_univ_eq_one] at hr
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  linarith

theorem refinedKrylovAlgorithm_tail_success_of_budget {b m k s n : ℕ}
    (hm : 0 < m) (hk0 : 0 < k) (hkb : k ≤ b)
    (A : Matrix (Fin (m + k)) (Fin b) ℝ) (hs : 2 * k + 2 ≤ s)
    {p γ ε : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 ≤ ε)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s (m + k)) < n)
    (hbudget : (k : ℝ) * (γ / 2) *
      ((canonicalOrderedSpectrum (m + k) (symmetricRightGram Aᵀ)).value
        (⟨m - 1, by omega⟩ : Fin (m + k))) ^ (p / 2) ≤ ε * optimalSchattenPower p A k) :
    19 / 20 ≤ (refinedKrylovAlgorithm.{u} (m + k) b k s n (by omega) hkb).law.real
      (rectangularSchattenSuccess p ε
        (refinedKrylovAlgorithm.{u} (m + k) b k s n (by omega) hkb).policy A) := by
  rw [refinedKrylovAlgorithm_success_probability (by omega) hkb (by linarith : 0 < p)]
  exact refinedKrylovPolicy_tail_success_of_budget hm hk0 hkb A hs hp hp2 hγ hγ1 hε hn hbudget

end
end LowRank
