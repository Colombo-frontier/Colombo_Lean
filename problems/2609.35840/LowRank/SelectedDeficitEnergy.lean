import LowRank.SelectedFilteredRitz
import LowRank.SpectralDeficitEnergy

/-! Deficit energy on a fixed spectral tail, after selecting columns of
the right inverse for the full head block. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem frobeniusSq_selected_columns_le {m k r : ℕ}
    (B : Matrix (Fin m) (Fin k) ℝ) (f : Fin r → Fin k) (hf : Function.Injective f) :
    frobeniusSq (B.submatrix id f) ≤ frobeniusSq B := by
  unfold frobeniusSq
  apply Finset.sum_le_sum
  intro i _
  calc
    ∑ j : Fin r, (B.submatrix id f i j) ^ 2 =
        ∑ j ∈ Finset.univ.image f, (B i j) ^ 2 := by
      rw [Finset.sum_image]
      · rfl
      · intro x _ y _ h
        exact hf h
    _ ≤ ∑ j : Fin k, (B i j) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      exact sq_nonneg _

theorem spectralDeficitMatrix_frobeniusSq_le_tail {a b m : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (f : Fin m → Fin b) (hf : Function.Injective f) {t L : ℝ}
    (ht : 0 ≤ t) (hl : ∀ i, sp.value (f i) ≤ L) :
    frobeniusSq (spectralDeficitMatrix A sp f t) ≤ (m : ℝ) * t * L := by
  rw [spectralDeficitMatrix_frobeniusSq A sp f hf]
  calc
    _ ≤ ∑ _ : Fin m, t * L := by
      apply Finset.sum_le_sum
      intro i _
      have hv := sp.value_nonneg (rightGram_posSemidef A) (f i)
      have hd : max 0 (t - sp.value (f i)) ≤ t := max_le ht (by linarith)
      exact mul_le_mul hd (hl i) hv ht
    _ = _ := by simp [mul_assoc]

theorem spectralDeficit_selected_startingBlock_le {a m k s r : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (U : Matrix (Fin a) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ)
    (f : Fin r → Fin k) (hf : Function.Injective f) {t α : ℝ}
    (hα : 0 < α) (hh : ∀ j : Fin r, α ≤ sp.value ((f j).natAdd m)) :
    weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
      ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd k) id *
        (R * diagonal (fun j : Fin k => (Real.sqrt (sp.value (j.natAdd m)))⁻¹)).submatrix id f) ≤
      α⁻¹ * frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd k) t * U) * R) := by
  have hsub : (R * diagonal (fun j : Fin k => (Real.sqrt (sp.value (j.natAdd m)))⁻¹)).submatrix id f =
      R.submatrix id f * diagonal (fun j => (Real.sqrt (sp.value ((f j).natAdd m)))⁻¹) := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_diagonal]
  rw [hsub, weightedFrobeniusSq_eq_sqrt_diagonal _ (fun _ => le_max_left _ _),
    spectral_startingBlock_rows]
  have he : diagonal (fun i : Fin m => Real.sqrt (max 0 (t - sp.value (i.castAdd k)))) *
      (((A * sp.basis.submatrix id (Fin.castAdd k))ᵀ * U) *
        (R.submatrix id f * diagonal (fun j : Fin r => (Real.sqrt (sp.value ((f j).natAdd m)))⁻¹))) =
      (((spectralDeficitMatrix A sp (Fin.castAdd k) t * U) * R).submatrix id f) *
        diagonal (fun j : Fin r => (Real.sqrt (sp.value ((f j).natAdd m)))⁻¹) := by
    have hc : ((spectralDeficitMatrix A sp (Fin.castAdd k) t * U) * R).submatrix id f =
        (spectralDeficitMatrix A sp (Fin.castAdd k) t * U) * R.submatrix id f := by ext i j; rfl
    rw [hc]
    simp only [spectralDeficitMatrix, Matrix.mul_assoc]
  rw [he]
  apply le_trans (frobeniusSq_mul_diagonal_le _ _ ?_)
    (mul_le_mul_of_nonneg_left (frobeniusSq_selected_columns_le _ f hf) (inv_nonneg.mpr hα.le))
  intro j
  rw [inv_pow, Real.sq_sqrt (hα.le.trans (hh j))]
  exact inv_anti₀ hα (hh j)

end
end LowRank
