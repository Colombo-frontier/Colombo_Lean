import LowRank.FilteredRitzLower
import LowRank.KrylovGaussianGapTail

/-! The below-threshold spectral deficit has bounded deterministic energy.
This makes a Gaussian tail estimate independent of any spectral gap. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def spectralDeficitMatrix {a b m : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : Fin m → Fin b) (t : ℝ) :
    Matrix (Fin m) (Fin a) ℝ :=
  diagonal (fun i => Real.sqrt (max 0 (t - sp.value (f i)))) * (A * sp.basis.submatrix id f)ᵀ

theorem spectralDeficitMatrix_frobeniusSq {a b m : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (f : Fin m → Fin b) (hf : Function.Injective f) (t : ℝ) :
    frobeniusSq (spectralDeficitMatrix A sp f t) =
      ∑ i, max 0 (t - sp.value (f i)) * sp.value (f i) := by
  let D := diagonal (fun i => Real.sqrt (max 0 (t - sp.value (f i))))
  have he : spectralDeficitMatrix A sp f t * (spectralDeficitMatrix A sp f t)ᵀ =
      D * ((A * sp.basis.submatrix id f)ᵀ * (A * sp.basis.submatrix id f)) * D := by
    simp only [spectralDeficitMatrix, D, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [frobeniusSq_eq_trace, he, spectral_subcolumns_gram A sp f hf]
  simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  have h := Real.sq_sqrt (le_max_left 0 (t - sp.value (f i)))
  calc
    _ = Real.sqrt (max 0 (t - sp.value (f i))) ^ 2 * sp.value (f i) := by ring
    _ = _ := by rw [h]

theorem spectralDeficitMatrix_frobeniusSq_le {a b m : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (f : Fin m → Fin b) (hf : Function.Injective f) {t : ℝ} (ht : 0 ≤ t) :
    frobeniusSq (spectralDeficitMatrix A sp f t) ≤ (m : ℝ) * t ^ 2 := by
  rw [spectralDeficitMatrix_frobeniusSq A sp f hf]
  calc
    _ ≤ ∑ _ : Fin m, t ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hval := sp.value_nonneg (rightGram_posSemidef A) (f i)
      by_cases hi : sp.value (f i) ≤ t
      · have hd : max 0 (t - sp.value (f i)) ≤ t := max_le ht (by linarith)
        simpa only [pow_two] using mul_le_mul hd hi hval ht
      · rw [max_eq_left (by linarith : t - sp.value (f i) ≤ 0), zero_mul]
        exact sq_nonneg t
    _ = _ := by simp

theorem frobeniusSq_mul_diagonal_le {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ)
    (c : Fin k → ℝ) {r : ℝ} (hc : ∀ j, c j ^ 2 ≤ r) :
    frobeniusSq (B * diagonal c) ≤ r * frobeniusSq B := by
  simp only [frobeniusSq, Matrix.mul_diagonal, mul_pow, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hc j) (sq_nonneg (B i j))

theorem spectralDeficit_scaled_startingBlock_le {a m k s : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (U : Matrix (Fin a) (Fin s) ℝ) (R : Matrix (Fin s) (Fin k) ℝ)
    {t : ℝ} (ht : 0 < t) (hh : ∀ j : Fin k, t ≤ sp.value (j.natAdd m)) :
    weightedFrobeniusSq (fun i : Fin m => max 0 (t - sp.value (i.castAdd k)))
      ((sp.basisᵀ * (Aᵀ * U)).submatrix (Fin.castAdd k) id *
        (R * diagonal (fun j => (Real.sqrt (sp.value (j.natAdd m)))⁻¹))) ≤
      t⁻¹ * frobeniusSq ((spectralDeficitMatrix A sp (Fin.castAdd k) t * U) * R) := by
  rw [weightedFrobeniusSq_eq_sqrt_diagonal _ (fun _ => le_max_left _ _),
    spectral_startingBlock_rows]
  have he : diagonal (fun i : Fin m => Real.sqrt (max 0 (t - sp.value (i.castAdd k)))) *
      (((A * sp.basis.submatrix id (Fin.castAdd k))ᵀ * U) *
        (R * diagonal (fun j : Fin k => (Real.sqrt (sp.value (j.natAdd m)))⁻¹))) =
      ((spectralDeficitMatrix A sp (Fin.castAdd k) t * U) * R) *
        diagonal (fun j : Fin k => (Real.sqrt (sp.value (j.natAdd m)))⁻¹) := by
    simp only [spectralDeficitMatrix, Matrix.mul_assoc]
  rw [he]
  apply frobeniusSq_mul_diagonal_le
  intro j
  rw [inv_pow, Real.sq_sqrt (ht.le.trans (hh j))]
  exact inv_anti₀ ht (hh j)

end
end LowRank
