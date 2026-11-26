import LowRank.SpectralPowers
import LowRank.CompressionScalar

/-! Real matrix compression power sums: the minimum is the sum of powers of
the smallest eigenvalues. On a positive fixed spectral interval, the excess
controls the trace deficit with a constant independent of matrix dimension. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem compression_isHermitian {d m : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (B : Matrix (Fin d) (Fin m) ℝ) : (Bᵀ * A * B).IsHermitian := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_mul B hA

def bottomPowerTrace {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (m : ℕ) (hm : m ≤ d) (r : ℝ) : ℝ :=
  ∑ i : Fin m, (orderedMatrixSpectrum hA).value (i.castLE hm) ^ r

theorem compression_power_ge_bottom {d m : ℕ} (hm : m ≤ d)
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef)
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1) {r : ℝ} (hr : 0 ≤ r) :
    bottomPowerTrace hA.isHermitian m hm r ≤
      symmetricPowerTrace (compression_isHermitian hA.isHermitian B) r := by
  apply Finset.sum_le_sum
  intro i _
  exact Real.rpow_le_rpow ((orderedMatrixSpectrum hA.isHermitian).value_nonneg hA _)
    (ordered_compression_eigenvalue_le hm _ _ B hB rfl i) hr

def firstEigenvectors {d m : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hm : m ≤ d) : Matrix (Fin d) (Fin m) ℝ :=
  (orderedMatrixSpectrum hA).basis.submatrix id (Fin.castLE hm)

theorem firstEigenvectors_orthogonal {d m : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hm : m ≤ d) :
    (firstEigenvectors hA hm)ᵀ * firstEigenvectors hA hm = 1 := by
  have h := compressed_submatrix (orderedMatrixSpectrum hA).basis
    (1 : Matrix (Fin d) (Fin d) ℝ) (Fin.castLE hm)
  simpa only [Matrix.mul_one, (orderedMatrixSpectrum hA).orthogonal,
    Matrix.submatrix_one _ (Fin.castLE_injective hm)] using h

theorem firstEigenvectors_compression {d m : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hm : m ≤ d) :
    (firstEigenvectors hA hm)ᵀ * A * firstEigenvectors hA hm =
      diagonal (fun i : Fin m => (orderedMatrixSpectrum hA).value (i.castLE hm)) := by
  rw [firstEigenvectors, compressed_submatrix, (orderedMatrixSpectrum hA).diagonalizes,
    Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)]
  rfl

theorem firstEigenvectors_power {d m : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hm : m ≤ d) (r : ℝ) :
    symmetricPowerTrace (compression_isHermitian hA (firstEigenvectors hA hm)) r =
      bottomPowerTrace hA m hm r := by
  let sp : OrderedMatrixSpectrum ((firstEigenvectors hA hm)ᵀ * A * firstEigenvectors hA hm) := {
    value := fun i => (orderedMatrixSpectrum hA).value (i.castLE hm)
    basis := 1
    increasing := fun _ _ hij => (orderedMatrixSpectrum hA).increasing hij
    orthogonal := by simp
    diagonalizes := by simpa only [transpose_one, one_mul, mul_one] using firstEigenvectors_compression hA hm }
  exact symmetricPowerTrace_eq _ sp r

theorem bottomPowerTrace_isLeast {d m : ℕ} (hm : m ≤ d)
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) {r : ℝ} (hr : 0 ≤ r) :
    IsLeast {z : ℝ | ∃ B : Matrix (Fin d) (Fin m) ℝ, Bᵀ * B = 1 ∧
      z = symmetricPowerTrace (compression_isHermitian hA.isHermitian B) r}
      (bottomPowerTrace hA.isHermitian m hm r) := by
  constructor
  · exact ⟨firstEigenvectors hA.isHermitian hm, firstEigenvectors_orthogonal _ _,
      (firstEigenvectors_power _ _ _).symm⟩
  · intro z hz
    obtain ⟨B, hB, rfl⟩ := hz
    exact compression_power_ge_bottom hm hA B hB hr

theorem exists_uniform_compression_power_slope {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ {d m : ℕ} (hm : m ≤ d) {A : Matrix (Fin d) (Fin d) ℝ}
      (hA : A.IsHermitian) (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1),
      LoewnerLE (a • 1) A → LoewnerLE A (b • 1) →
      c * ((Bᵀ * A * B).trace - bottomPowerTrace hA m hm 1) ≤
        symmetricPowerTrace (compression_isHermitian hA B) r - bottomPowerTrace hA m hm r := by
  obtain ⟨c, hc, hslope⟩ := exists_positive_rpow_slope ha hab hr
  refine ⟨c, hc, ?_⟩
  intro d m hm A hA B hB hlow hupp
  let spA := orderedMatrixSpectrum hA
  let spC := orderedMatrixSpectrum (compression_isHermitian hA B)
  obtain ⟨hclow, hcupp⟩ := orthogonal_compression_interval B hB hlow hupp
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
    hslope (spA.value (i.castLE hm)) (spA.value_mem_Icc hlow hupp _)
      (spC.value i) (spC.value_mem_Icc hclow hcupp i)
      (ordered_compression_eigenvalue_le hm spA spC B hB rfl i))
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  rw [← spC.trace] at hsum
  simpa only [bottomPowerTrace, symmetricPowerTrace, Real.rpow_one, spA, spC] using hsum

theorem compression_trace_deficit {d m : ℕ} {A P : Matrix (Fin d) (Fin d) ℝ}
    (B : Matrix (Fin d) (Fin m) ℝ) (hQ : B * Bᵀ = 1 - P) (baseline : ℝ) :
    (Bᵀ * A * B).trace - baseline = A.trace - baseline - (P * A).trace := by
  rw [Matrix.trace_mul_cycle, hQ, sub_mul, one_mul, Matrix.trace_sub]
  ring

end
end LowRank
