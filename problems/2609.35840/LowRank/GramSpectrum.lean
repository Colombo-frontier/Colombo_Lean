import LowRank.MatrixSchattenCompression

/-! For a positive semidefinite symmetric matrix, the ordered Gram
eigenvalues are the squares of the ordered matrix eigenvalues. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem diagonal_loewner_of_le {d : ℕ} {lam mu : Fin d → ℝ}
    (h : ∀ i, lam i ≤ mu i) : LoewnerLE (diagonal lam) (diagonal mu) := by
  change (diagonal mu - diagonal lam).PosSemidef
  rw [Matrix.diagonal_sub]
  exact Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (h i))

theorem real_diagonal_const {d : ℕ} (a : ℝ) :
    (diagonal (fun _ : Fin d => a) : Matrix (Fin d) (Fin d) ℝ) = a • 1 := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal, Matrix.one_apply, hij]

theorem OrderedMatrixSpectrum.loewner_interval {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) {a b : ℝ} (h : ∀ i, sp.value i ∈ Set.Icc a b) :
    LoewnerLE (a • 1) A ∧ LoewnerLE A (b • 1) := by
  have hl := loewner_congruence (diagonal_loewner_of_le (fun i => (h i).1)) sp.basisᵀ
  have hu := loewner_congruence (diagonal_loewner_of_le (fun i => (h i).2)) sp.basisᵀ
  simp only [Matrix.transpose_transpose, ← sp.reconstruct, real_diagonal_const,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, sp.orthogonal_right] at hl hu
  exact ⟨hl, hu⟩

def OrderedMatrixSpectrum.gram {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum H) (hpos : ∀ i, 0 ≤ sp.value i) :
    OrderedMatrixSpectrum (Hᵀ * H) where
  value := fun i => sp.value i ^ 2
  basis := sp.basis
  increasing := by
    intro i j hij
    have h := sp.increasing hij
    exact (sq_le_sq₀ (hpos i) (hpos j)).2 h
  orthogonal := sp.orthogonal
  diagonalizes := by
    calc
      sp.basisᵀ * (Hᵀ * H) * sp.basis = (H * sp.basis)ᵀ * (H * sp.basis) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (sp.basis * diagonal sp.value)ᵀ * (sp.basis * diagonal sp.value) := by
        rw [sp.mul_basis]
      _ = diagonal sp.value * (sp.basisᵀ * sp.basis) * diagonal sp.value := by
        simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
      _ = diagonal (fun i => sp.value i ^ 2) := by
        simp only [sp.orthogonal, Matrix.mul_one, Matrix.diagonal_mul_diagonal, pow_two]

theorem symmetric_gram_spectral_interval {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.IsHermitian) {a b : ℝ} (ha : 0 < a)
    (hlow : LoewnerLE (a • 1) H) (hupp : LoewnerLE H (b • 1)) :
    LoewnerLE ((a ^ 2) • 1) (Hᵀ * H) ∧ LoewnerLE (Hᵀ * H) ((b ^ 2) • 1) := by
  let sp := orderedMatrixSpectrum hH
  have hv := sp.value_mem_Icc hlow hupp
  have hn (i : Fin d) : 0 ≤ sp.value i := ha.le.trans (hv i).1
  apply (sp.gram hn).loewner_interval
  intro i
  change a ^ 2 ≤ sp.value i ^ 2 ∧ sp.value i ^ 2 ≤ b ^ 2
  constructor <;> nlinarith [(hv i).1, (hv i).2, hn i]

theorem ordered_gram_values_eq_squares {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosSemidef) :
    (orderedMatrixSpectrum (rightGram_posSemidef H).isHermitian).value =
      fun i => (orderedMatrixSpectrum hH.isHermitian).value i ^ 2 :=
  (orderedMatrixSpectrum (rightGram_posSemidef H).isHermitian).value_unique
    ((orderedMatrixSpectrum hH.isHermitian).gram (fun i =>
      (orderedMatrixSpectrum hH.isHermitian).value_nonneg hH i))

end
end LowRank
