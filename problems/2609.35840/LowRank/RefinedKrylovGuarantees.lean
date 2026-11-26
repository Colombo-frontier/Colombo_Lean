import LowRank.RefinedKrylovAlgorithm
import LowRank.KrylovFrobeniusGap

/-! Deterministic all-p error guarantees for the actual refined Krylov
output, and a Schatten-2 probability guarantee under a spectral gap. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators ENNReal
noncomputable section
universe u

theorem refinedKrylovPolicy_success_of_ritz_errors {a b k s n : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin b) (Fin s) ℝ) {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 ≤ ε)
    (e : Fin k → ℝ) (he : ∀ j, 0 ≤ e j)
    (happrox : ∀ j, (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value
      (lastColumnIndex a k hka j) - e j ≤
        (canonicalOrderedSpectrum a (symmetricRightGram (Aᵀ *
          columnRangeProjector (krylovRightBlocks (krylovBlockData Aᵀ n U))))).value
            (lastColumnIndex a k hka j))
    (hbudget : (∑ j, max 1 (p / 2) * e j *
      ((canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value
        (lastColumnIndex a k hka j)) ^ (p / 2 - 1)) ≤ ε * optimalSchattenPower p A k) :
    U ∈ rectangularSchattenSuccess p ε (refinedKrylovPolicy a b k s n hka hkb) A := by
  change schattenNorm p (A * (1 -
    runBoundedRectangular a b (krylovQueryBudget s 0 n)
      (refinedKrylovPolicy a b k s n hka hkb) A U *
    (runBoundedRectangular a b (krylovQueryBudget s 0 n)
      (refinedKrylovPolicy a b k s n hka hkb) A U)ᵀ)) ≤ _
  rw [refinedKrylovPolicy_run]
  exact refinedRitzColumns_relative_of_ritz_errors hka hkb A
    (columnRangeProjector_isProjector _) hp hε e he happrox hbudget

theorem refinedRitzColumns_frobenius_residual_le_weighted {b m k : ℕ}
    (hkb : k ≤ b) (A : Matrix (Fin (m + k)) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀᵀ * Aᵀ))
    {P : Matrix (Fin (m + k)) (Fin (m + k)) ℝ} (hP : IsOrthogonalProjector P) :
    let Z := refinedRitzColumns (m + k) b k (by omega) hkb (Aᵀ * P)
    frobeniusSq (A * (1 - Z * Zᵀ)) ≤
      frobeniusSq (Aᵀ * sp.basis.submatrix id (Fin.castAdd k)) +
        2 * frobeniusSq ((1 - P) * (sp.basis.submatrix id (Fin.natAdd m) *
          diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m))))) := by
  have hr := refinedRitzColumns_residual_power (by omega : k ≤ m + k) hkb A hP
    (by norm_num : (1 : ℝ) ≤ 2)
  dsimp only at hr ⊢
  simp only [schattenPower_two] at hr
  have hV := orthogonal_subcolumns sp.basis sp.orthogonal (Fin.natAdd m) (Fin.natAddEmb m).injective
  have hc := optimalColumnSelector_captures_max_energy (by omega : k ≤ m + k)
    (Aᵀ * P) _ hV
  have he := spectral_projection_energy_loss Aᵀ sp (Fin.natAdd m) hP
  have hs := frobeniusSq_spectral_split Aᵀ sp
  rw [frobeniusSq_transpose] at hs
  linarith

theorem refinedKrylovPolicy_frobenius_success_of_weighted {b m k s n : ℕ}
    (hkb : k ≤ b) (A : Matrix (Fin (m + k)) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀᵀ * Aᵀ)) (U : Matrix (Fin b) (Fin s) ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : frobeniusSq ((1 - columnRangeProjector (krylovRightBlocks (krylovBlockData Aᵀ n U))) *
      (sp.basis.submatrix id (Fin.natAdd m) *
        diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m))))) ≤
          ε * frobeniusSq (Aᵀ * sp.basis.submatrix id (Fin.castAdd k))) :
    U ∈ rectangularSchattenSuccess 2 ε (refinedKrylovPolicy (m + k) b k s n (by omega) hkb) A := by
  change schattenNorm 2 (A * (1 -
    runBoundedRectangular (m + k) b (krylovQueryBudget s 0 n)
      (refinedKrylovPolicy (m + k) b k s n (by omega) hkb) A U *
    (runBoundedRectangular (m + k) b (krylovQueryBudget s 0 n)
      (refinedKrylovPolicy (m + k) b k s n (by omega) hkb) A U)ᵀ)) ≤ _
  rw [refinedKrylovPolicy_run]
  apply schattenNorm_two_relative_of_frobenius hkb A _ hε
  have hr := refinedRitzColumns_frobenius_residual_le_weighted hkb A sp
    (columnRangeProjector_isProjector (krylovRightBlocks (krylovBlockData Aᵀ n U)))
  dsimp only at hr
  rw [frobeniusSq_spectral_tail_eq_optimum Aᵀ sp,
    optimalSchattenPower_transpose (by omega) hkb A (by norm_num : (0 : ℝ) < 2)] at hr h
  linarith

theorem refinedKrylovPolicy_frobenius_gap_bad_le {b m k s n : ℕ}
    (hkb : k ≤ b) (A : Matrix (Fin (m + k)) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀᵀ * Aᵀ)) (hs : 2 * k + 2 ≤ s)
    {t γ ε : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hn : chebyshevFilterDegree γ (weightedKrylovTolerance ε s) < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    (iidMatrixLaw b s 1)
      (rectangularSchattenSuccess 2 ε
        (refinedKrylovPolicy (m + k) b k s n (by omega) hkb) A)ᶜ ≤ 1 / 20 := by
  refine (measure_mono ?_).trans
    (krylov_gaussian_weighted_relative_gap_bad_le Aᵀ sp hs ht hγ hγ1 hε hn hl hh)
  intro U hU
  change ε * frobeniusSq (Aᵀ * sp.basis.submatrix id (Fin.castAdd k)) < _
  by_contra! h
  exact hU (refinedKrylovPolicy_frobenius_success_of_weighted hkb A sp U hε.le h)

theorem refinedKrylovPolicy_frobenius_gap_success {b m k s n : ℕ}
    (hkb : k ≤ b) (A : Matrix (Fin (m + k)) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀᵀ * Aᵀ)) (hs : 2 * k + 2 ≤ s)
    {t γ ε : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hn : chebyshevFilterDegree γ (weightedKrylovTolerance ε s) < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    19 / 20 ≤ (iidMatrixLaw b s 1).real
      (rectangularSchattenSuccess 2 ε
        (refinedKrylovPolicy (m + k) b k s n (by omega) hkb) A) := by
  have hbad := refinedKrylovPolicy_frobenius_gap_bad_le hkb A sp hs ht hγ hγ1 hε hn hl hh
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 20 : ℝ≥0∞) ≠ ∞) hbad
  have hm := measurableSet_rectangularSchattenSuccess hkb (by norm_num : (0 : ℝ) < 2) ε
    (refinedKrylovPolicy (m + k) b k s n (by omega) hkb) A
  change (iidMatrixLaw b s 1).real _ ≤ _ at hr
  rw [measureReal_compl hm, measureReal_univ_eq_one] at hr
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  linarith

theorem refinedKrylovAlgorithm_frobenius_gap_success {b m k s n : ℕ}
    (hkb : k ≤ b) (A : Matrix (Fin (m + k)) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀᵀ * Aᵀ)) (hs : 2 * k + 2 ≤ s)
    {t γ ε : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hn : chebyshevFilterDegree γ (weightedKrylovTolerance ε s) < n)
    (hl : ∀ i : Fin m, sp.value (i.castAdd k) ≤ t)
    (hh : ∀ j : Fin k, t * (1 + γ / 2) ≤ sp.value (j.natAdd m)) :
    19 / 20 ≤ (refinedKrylovAlgorithm.{u} (m + k) b k s n (by omega) hkb).law.real
      (rectangularSchattenSuccess 2 ε
        (refinedKrylovAlgorithm.{u} (m + k) b k s n (by omega) hkb).policy A) := by
  rw [refinedKrylovAlgorithm_success_probability (by omega) hkb (by norm_num : (0 : ℝ) < 2)]
  exact refinedKrylovPolicy_frobenius_gap_success hkb A sp hs ht hγ hγ1 hε hn hl hh

end
end LowRank
