import LowRank.SpectralDiagonalJensen
import LowRank.SchattenProjectorContraction

/-! Complementary orthogonal compressions satisfy a convex spectral-sum
inequality. Applied to a Gram matrix, this gives Schatten-power pinching
for p at least two. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem convex_sum_diagonal_le_spectral_reindex {d : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum H) (e : Fin d ≃ ι) (J : Matrix (Fin d) ι ℝ)
    (hJ : Jᵀ * J = 1) {S : Set ℝ} {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ S φ) (hS : ∀ j, sp.value j ∈ S) :
    (∑ i, φ ((Jᵀ * H * J) i i)) ≤ ∑ j, φ (sp.value j) := by
  let U := J.submatrix id e
  have hU : Uᵀ * U = 1 := by
    change Jᵀ.submatrix e id * J.submatrix id e = 1
    have h := Matrix.submatrix_mul_equiv Jᵀ J e (Equiv.refl (Fin d)) e
    simpa only [Equiv.coe_refl, hJ, Matrix.submatrix_one_equiv] using h
  have hUd : Uᵀ * H * U = (Jᵀ * H * J).submatrix e e := by
    change Jᵀ.submatrix e id * H * J.submatrix id e = _
    have hfirst : Jᵀ.submatrix e id * H = (Jᵀ * H).submatrix e id := by
      simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
        Matrix.submatrix_mul_equiv Jᵀ H e (Equiv.refl (Fin d)) id
    rw [hfirst]
    simpa only [Equiv.coe_refl] using
      Matrix.submatrix_mul_equiv (Jᵀ * H) J e (Equiv.refl (Fin d)) e
  have h := convex_sum_diagonal_le_spectral sp U hU hφ hS
  rw [hUd] at h
  change (∑ i, φ ((Jᵀ * H * J) (e i) (e i))) ≤ _ at h
  rwa [Equiv.sum_comp e (fun i => φ ((Jᵀ * H * J) i i))] at h

theorem convex_complementary_compression_sum_le {k m : ℕ}
    {H : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (sp : OrderedMatrixSpectrum H)
    (C : Matrix (Fin (k + m)) (Fin k) ℝ) (hC : Cᵀ * C = 1)
    (B : Matrix (Fin (k + m)) (Fin m) ℝ) (hB : Bᵀ * B = 1) (hCB : Cᵀ * B = 0)
    (spC : OrderedMatrixSpectrum (Cᵀ * H * C)) (spB : OrderedMatrixSpectrum (Bᵀ * H * B))
    {S : Set ℝ} {φ : ℝ → ℝ} (hφ : ConvexOn ℝ S φ) (hS : ∀ j, sp.value j ∈ S) :
    (∑ i, φ (spC.value i)) + (∑ j, φ (spB.value j)) ≤ ∑ l, φ (sp.value l) := by
  let E := C * spC.basis
  let F := B * spB.basis
  have hE : Eᵀ * E = 1 := by
    calc
      _ = spC.basisᵀ * (Cᵀ * C) * spC.basis := by simp only [E, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hC, Matrix.mul_one, spC.orthogonal]
  have hF : Fᵀ * F = 1 := by
    calc
      _ = spB.basisᵀ * (Bᵀ * B) * spB.basis := by simp only [F, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hB, Matrix.mul_one, spB.orthogonal]
  have hEF : Eᵀ * F = 0 := by
    calc
      _ = spC.basisᵀ * (Cᵀ * B) * spB.basis := by simp only [E, F, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hCB, Matrix.mul_zero, Matrix.zero_mul]
  have hFE : Fᵀ * E = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose hEF
  have hEHE : Eᵀ * H * E = diagonal spC.value := by
    calc
      _ = spC.basisᵀ * (Cᵀ * H * C) * spC.basis := by simp only [E, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := spC.diagonalizes
  have hFHF : Fᵀ * H * F = diagonal spB.value := by
    calc
      _ = spB.basisᵀ * (Bᵀ * H * B) * spB.basis := by simp only [F, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := spB.diagonalizes
  have hJ : (joinColumns E F)ᵀ * joinColumns E F = 1 := by
    rw [joinColumns_gram, hE, hEF, hFE, hF]
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  have hdiag (i : Fin k ⊕ Fin m) :
      ((joinColumns E F)ᵀ * H * joinColumns E F) i i = Sum.elim spC.value spB.value i := by
    rw [joinColumns_compression, hEHE, hFHF]
    cases i <;> simp [Matrix.fromBlocks]
  have h := convex_sum_diagonal_le_spectral_reindex sp finSumFinEquiv.symm
    (joinColumns E F) hJ hφ hS
  simp only [hdiag, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at h
  exact h

theorem symmetricPowerTrace_complementary_compressions_le {k m : ℕ}
    {H : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} (hH : H.PosSemidef)
    (C : Matrix (Fin (k + m)) (Fin k) ℝ) (hC : Cᵀ * C = 1)
    (B : Matrix (Fin (k + m)) (Fin m) ℝ) (hB : Bᵀ * B = 1) (hCB : Cᵀ * B = 0)
    {r : ℝ} (hr : 1 ≤ r) :
    symmetricPowerTrace (compression_isHermitian hH.isHermitian C) r +
      symmetricPowerTrace (compression_isHermitian hH.isHermitian B) r ≤
        symmetricPowerTrace hH.isHermitian r :=
  convex_complementary_compression_sum_le (orderedMatrixSpectrum hH.isHermitian)
    C hC B hB hCB (orderedMatrixSpectrum (compression_isHermitian hH.isHermitian C))
    (orderedMatrixSpectrum (compression_isHermitian hH.isHermitian B))
    (convexOn_rpow hr) (fun j => (orderedMatrixSpectrum hH.isHermitian).value_nonneg hH j)

theorem schattenPower_projector_eq_compression {a b m : ℕ} {p : ℝ} (hp : 0 < p)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ}
    (B : Matrix (Fin b) (Fin m) ℝ) (hB : Bᵀ * B = 1) (hBB : B * Bᵀ = P) :
    schattenPower p (A * P) =
      symmetricPowerTrace (compression_isHermitian (rightGram_posSemidef A).isHermitian B) (p / 2) := by
  rw [← hBB, ← Matrix.mul_assoc, schattenPower_right_extension hp _ B hB,
    schattenPower_eq_symmetricPowerTrace]
  apply symmetricPowerTrace_congr
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem schattenPower_projector_pinching {a b : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ}
    (hP : IsOrthogonalProjector P) :
    schattenPower p (A * P) + schattenPower p (A * (1 - P)) ≤ schattenPower p A := by
  have hp0 : 0 < p := by linarith
  obtain ⟨B, hB, hBB⟩ := projector_basis_factorization hP rfl
  obtain ⟨k, hb⟩ := Nat.exists_eq_add_of_le' (orthogonal_columns_dimension_le B hB)
  generalize hm : P.rank = m at B hB hBB hb
  subst b
  obtain ⟨C, hC, hCC, hCB⟩ := exists_orthogonal_complement_columns B hB
  rw [hBB] at hCC
  rw [schattenPower_projector_eq_compression hp0 A B hB hBB,
    schattenPower_projector_eq_compression hp0 A C hC hCC, schattenPower_eq_symmetricPowerTrace,
    add_comm]
  exact symmetricPowerTrace_complementary_compressions_le (rightGram_posSemidef A)
    C hC B hB hCB (by linarith)

end
end LowRank
