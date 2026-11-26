import LowRank.RitzFrobeniusRelative
import LowRank.KrylovGaussianGapConstant
import LowRank.KrylovColumnAlgorithm

/-! Actual relative Schatten-2 success for the measurable Gaussian Krylov
algorithm on a separated spectrum, with its original column output and
the exact two-sided query budget. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

theorem krylovColumnPolicy_frobenius_success_of_weighted {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (U : Matrix (Fin a) (Fin s) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) *
      (sp.basis.submatrix id (Fin.natAdd m) *
        diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m))))) ≤
          ε * frobeniusSq (A * sp.basis.submatrix id (Fin.castAdd k))) :
    U ∈ rectangularSchattenSuccess 2 ε (krylovColumnPolicy a (m + k) k s n (by omega)) A := by
  change schattenNorm 2 (A * (1 -
    runBoundedRectangular a (m + k) (krylovQueryBudget s 0 n)
      (krylovColumnPolicy a (m + k) k s n (by omega)) A U *
    (runBoundedRectangular a (m + k) (krylovQueryBudget s 0 n)
      (krylovColumnPolicy a (m + k) k s n (by omega)) A U)ᵀ)) ≤ _
  rw [krylovColumnPolicy_run]
  exact ritz_frobenius_relative_of_weighted_error A sp (columnRangeProjector_isProjector _) hε h

theorem krylovColumnPolicy_frobenius_gap_bad_le {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hs : 2 * k + 2 ≤ s)
    {t γ ε : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hn : chebyshevFilterDegree γ (weightedKrylovTolerance ε s) < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    (iidMatrixLaw a s 1)
      (rectangularSchattenSuccess 2 ε (krylovColumnPolicy a (m + k) k s n (by omega)) A)ᶜ ≤ 1 / 20 := by
  refine (measure_mono ?_).trans (krylov_gaussian_weighted_relative_gap_bad_le A sp hs ht hγ hγ1 hε hn hl hh)
  intro U hU
  change ε * frobeniusSq (A * sp.basis.submatrix id (Fin.castAdd k)) < _
  by_contra! h
  exact hU (krylovColumnPolicy_frobenius_success_of_weighted A sp U hε.le h)

theorem krylovColumnPolicy_frobenius_gap_success {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hs : 2 * k + 2 ≤ s)
    {t γ ε : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hn : chebyshevFilterDegree γ (weightedKrylovTolerance ε s) < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    19 / 20 ≤ (iidMatrixLaw a s 1).real
      (rectangularSchattenSuccess 2 ε (krylovColumnPolicy a (m + k) k s n (by omega)) A) := by
  have hbad := krylovColumnPolicy_frobenius_gap_bad_le A sp hs ht hγ hγ1 hε hn hl hh
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 20 : ℝ≥0∞) ≠ ∞) hbad
  have hm := measurableSet_rectangularSchattenSuccess (by omega : k ≤ m + k)
    (by norm_num : (0 : ℝ) < 2) ε (krylovColumnPolicy a (m + k) k s n (by omega)) A
  change (iidMatrixLaw a s 1).real _ ≤ _ at hr
  rw [measureReal_compl hm, measureReal_univ_eq_one] at hr
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  linarith

theorem krylovColumnAlgorithm_frobenius_gap_success {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hs : 2 * k + 2 ≤ s)
    {t γ ε : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hn : chebyshevFilterDegree γ (weightedKrylovTolerance ε s) < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    19 / 20 ≤ (krylovColumnAlgorithm.{u} a (m + k) k s n (by omega)).law.real
      (rectangularSchattenSuccess 2 ε
        (krylovColumnAlgorithm.{u} a (m + k) k s n (by omega)).policy A) := by
  rw [krylovColumnAlgorithm_success_probability (by omega) (by norm_num : (0 : ℝ) < 2)]
  exact krylovColumnPolicy_frobenius_gap_success A sp hs ht hγ hγ1 hε hn hl hh

theorem weightedKrylovTolerance_le_one {ε : ℝ} {s : ℕ} (hε : ε ≤ 1) (hs : 0 < s) :
    weightedKrylovTolerance ε s ≤ 1 := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  rw [weightedKrylovTolerance, Real.sqrt_le_one]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1600 * (s : ℝ))).mpr
  linarith

theorem krylov_frobenius_gap_query_count {a b k s : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (U : Matrix (Fin a) (Fin s) ℝ) (hk : k ≤ b) (hs : 0 < s)
    {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let n := chebyshevFilterDegree γ (weightedKrylovTolerance ε s) + 1
    (((krylovColumnPolicy a b k s n hk).toProgram a b (krylovQueryBudget s 0 n) U).calls
      (rectangularOracle A) : ℝ) ≤
        2 * (s : ℝ) * (2 * Real.log (2 / weightedKrylovTolerance ε s) / Real.sqrt γ + 2) := by
  dsimp only
  rw [krylovColumnPolicy_calls]
  have h := krylov_gap_query_count A U hγ (weightedKrylovTolerance_pos hε hs)
    (weightedKrylovTolerance_le_one hε1 hs)
  dsimp only at h
  rwa [krylovBlockPolicy_calls] at h

end
end LowRank
