import LowRank.ConfidentKrylovRitz
import LowRank.SchattenContinuity

/-! All selected Ritz values are controlled on one Gaussian Krylov run.
The union bound uses adjustable confidence and does not assert independence. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators ENNReal
noncomputable section

def krylovRelativeRitzEvent {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (k s n : ℕ) (hk : k ≤ b) (γ : ℝ) :
    Set (Matrix (Fin a) (Fin s) ℝ) :=
  {U | ∀ j : Fin k, sp.value (lastColumnIndex b k hk j) / (1 + γ / 2) ≤
    (canonicalOrderedSpectrum b (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
        (lastColumnIndex b k hk j)}

theorem measurable_krylovRestriction {a b s n : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    Measurable (fun U : Matrix (Fin a) (Fin s) ℝ =>
      A * columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))) := by
  have hr : Measurable (fun U : Matrix (Fin a) (Fin s) ℝ =>
      runBoundedRectangular a b (krylovQueryBudget s 0 n) (krylovBlockPolicy a b s n) A U) :=
    (measurable_runBoundedRectangular a b (krylovQueryBudget s 0 n) (krylovBlockPolicy a b s n)).comp
      (measurable_const.prodMk measurable_id)
  have h := (measurable_krylovCompressedMatrix a b s n).comp hr
  simpa only [Function.comp_def, krylovBlockPolicy_run, krylovCompressedMatrix_eq] using h

theorem measurable_krylovRitzValue {a b s n : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (i : Fin b) :
    Measurable (fun U : Matrix (Fin a) (Fin s) ℝ =>
      (canonicalOrderedSpectrum b (symmetricRightGram (A *
        columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value i) := by
  simp only [canonicalOrderedSpectrum_value]
  exact (continuous_gram_eigenvalue a b i).measurable.comp (measurable_krylovRestriction A)

theorem measurableSet_krylovRelativeRitzEvent {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (k s n : ℕ) (hk : k ≤ b) (γ : ℝ) :
    MeasurableSet (krylovRelativeRitzEvent A sp k s n hk γ) := by
  have he : krylovRelativeRitzEvent A sp k s n hk γ =
      ⋂ j : Fin k, {U | sp.value (lastColumnIndex b k hk j) / (1 + γ / 2) ≤
        (canonicalOrderedSpectrum b (symmetricRightGram (A *
          columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
            (lastColumnIndex b k hk j)} := by
    ext U
    simp only [krylovRelativeRitzEvent, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun j => measurableSet_le measurable_const (measurable_krylovRitzValue A _))

theorem krylov_simultaneous_relative_ritz_confidence_le {a b k s n : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hk : k ≤ b)
    (hs : 2 * k + 2 ≤ s) {γ q : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hq : 0 < q)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ q s b) < n) :
    (iidMatrixLaw a s 1) (krylovRelativeRitzEvent A sp k s n hk γ)ᶜ ≤
      ENNReal.ofReal ((k : ℝ) * (2 / q)) := by
  let E : Fin k → Set (Matrix (Fin a) (Fin s) ℝ) := fun j => {U |
    (canonicalOrderedSpectrum b (symmetricRightGram (A *
      columnRangeProjector (krylovRightBlocks (krylovBlockData A n U))))).value
        (lastColumnIndex b k hk j) < sp.value (lastColumnIndex b k hk j) / (1 + γ / 2)}
  have he : (krylovRelativeRitzEvent A sp k s n hk γ)ᶜ = ⋃ j : Fin k, E j := by
    ext U
    simp only [krylovRelativeRitzEvent, E, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_iUnion, not_forall, not_le]
  have hE (j : Fin k) : (iidMatrixLaw a s 1) (E j) ≤ ENNReal.ofReal (2 / q) := by
    apply krylov_gaussian_ritz_index_confidence_le A sp (lastColumnIndex b k hk j) _ hγ hγ1 hq hn
    have hi : (lastColumnIndex b k hk j).val = b - k + j.val := rfl
    rw [hi]
    omega
  rw [he]
  calc
    _ ≤ ∑ j : Fin k, (iidMatrixLaw a s 1) (E j) := by
      simpa only [tsum_fintype] using measure_iUnion_le E
    _ ≤ ∑ _ : Fin k, ENNReal.ofReal (2 / q) := Finset.sum_le_sum (fun j _ => hE j)
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun (_ : Fin k) _ => by positivity :
        ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ (2 : ℝ) / q)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem krylov_simultaneous_relative_ritz_bad_le {a b k s n : ℕ} (hk0 : 0 < k)
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hk : k ≤ b)
    (hs : 2 * k + 2 ≤ s) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s b) < n) :
    (iidMatrixLaw a s 1) (krylovRelativeRitzEvent A sp k s n hk γ)ᶜ ≤ 1 / 20 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have h := krylov_simultaneous_relative_ritz_confidence_le A sp hk hs hγ hγ1
    (by positivity : 0 < 40 * (k : ℝ)) hn
  have he : (k : ℝ) * (2 / (40 * (k : ℝ))) = 1 / 20 := by field_simp; ring
  rw [he, ENNReal.ofReal_div_of_pos (by norm_num)] at h
  norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at h
  exact h

theorem krylov_simultaneous_relative_ritz_success {a b k s n : ℕ} (hk0 : 0 < k)
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hk : k ≤ b)
    (hs : 2 * k + 2 ≤ s) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hn : chebyshevFilterDegree γ (confidentRitzTolerance γ (40 * (k : ℝ)) s b) < n) :
    19 / 20 ≤ (iidMatrixLaw a s 1).real (krylovRelativeRitzEvent A sp k s n hk γ) := by
  have hbad := krylov_simultaneous_relative_ritz_bad_le hk0 A sp hk hs hγ hγ1 hn
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 20 : ℝ≥0∞) ≠ ∞) hbad
  change (iidMatrixLaw a s 1).real _ ≤ _ at hr
  rw [measureReal_compl (measurableSet_krylovRelativeRitzEvent A sp k s n hk γ),
    measureReal_univ_eq_one] at hr
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  linarith

end
end LowRank
