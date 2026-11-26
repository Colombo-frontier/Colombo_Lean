import LowRank.DiagonalInterlacing

/-! Poincare separation for arbitrary real symmetric compressions, plus
monotonicity and uniqueness of the ordered eigenvalue list. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem ordered_compression_eigenvalue_le_of_loewner {d m : ℕ} (hm : m ≤ d)
    {A : Matrix (Fin d) (Fin d) ℝ} {C : Matrix (Fin m) (Fin m) ℝ}
    (spA : OrderedMatrixSpectrum A) (spC : OrderedMatrixSpectrum C)
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1)
    (hcomp : LoewnerLE (Bᵀ * A * B) C) (i : Fin m) :
    spA.value (i.castLE hm) ≤ spC.value i := by
  let D := spA.basisᵀ * B * spC.basis
  have hD : Dᵀ * D = 1 := by
    dsimp only [D]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = spC.basisᵀ * (Bᵀ * (spA.basis * spA.basisᵀ) * B) * spC.basis := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [spA.orthogonal_right, Matrix.mul_one, hB, Matrix.mul_one, spC.orthogonal]
  have heq : Dᵀ * diagonal spA.value * D = spC.basisᵀ * (Bᵀ * A * B) * spC.basis := by
    dsimp only [D]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = spC.basisᵀ * (Bᵀ * (spA.basis * diagonal spA.value * spA.basisᵀ) * B) * spC.basis := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [← spA.reconstruct]
  have hdiag := loewner_congruence hcomp spC.basis
  rw [spC.diagonalizes, ← heq] at hdiag
  exact diagonal_compression_eigenvalue_le_of_loewner hm spA.value spC.value
    spA.increasing spC.increasing D hD hdiag i

theorem ordered_compression_eigenvalue_le {d m : ℕ} (hm : m ≤ d)
    {A : Matrix (Fin d) (Fin d) ℝ} {C : Matrix (Fin m) (Fin m) ℝ}
    (spA : OrderedMatrixSpectrum A) (spC : OrderedMatrixSpectrum C)
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1)
    (hcomp : Bᵀ * A * B = C) (i : Fin m) :
    spA.value (i.castLE hm) ≤ spC.value i := by
  apply ordered_compression_eigenvalue_le_of_loewner hm spA spC B hB _ i
  rw [LoewnerLE, hcomp, sub_self]
  exact Matrix.PosSemidef.zero

theorem ordered_eigenvalue_mono {d : ℕ} {A C : Matrix (Fin d) (Fin d) ℝ}
    (spA : OrderedMatrixSpectrum A) (spC : OrderedMatrixSpectrum C)
    (hAC : LoewnerLE A C) (i : Fin d) : spA.value i ≤ spC.value i := by
  exact ordered_compression_eigenvalue_le_of_loewner
    (Nat.le_refl d) spA spC (1 : Matrix (Fin d) (Fin d) ℝ) (by simp) (by simpa using hAC) i

theorem OrderedMatrixSpectrum.value_unique {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp sp' : OrderedMatrixSpectrum A) : sp.value = sp'.value := by
  have hAA : LoewnerLE A A := by rw [LoewnerLE, sub_self]; exact Matrix.PosSemidef.zero
  funext i
  exact le_antisymm (ordered_eigenvalue_mono sp sp' hAA i) (ordered_eigenvalue_mono sp' sp hAA i)

theorem orthogonal_compression_interval {d m : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    {a b : ℝ} (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1)
    (hlow : LoewnerLE (a • 1) A) (hupp : LoewnerLE A (b • 1)) :
    LoewnerLE (a • 1) (Bᵀ * A * B) ∧ LoewnerLE (Bᵀ * A * B) (b • 1) := by
  have hl := loewner_congruence hlow B
  have hu := loewner_congruence hupp B
  simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hB] using And.intro hl hu

end
end LowRank
