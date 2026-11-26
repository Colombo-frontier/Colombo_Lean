import LowRank.SpectralTraceInterchange
import LowRank.SpectralCompressionPinching

/-! Spectral sums for a general scalar function. For functions vanishing
at zero, isometric extension preserves the sum. Convex functions additionally
satisfy pinching by any orthogonal projector. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def symmetricFunctionTrace {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.IsHermitian) (φ : ℝ → ℝ) : ℝ := ∑ i, φ ((orderedMatrixSpectrum hH).value i)

theorem symmetricFunctionTrace_eq {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.IsHermitian) (sp : OrderedMatrixSpectrum H) (φ : ℝ → ℝ) :
    symmetricFunctionTrace hH φ = ∑ i, φ (sp.value i) := by
  unfold symmetricFunctionTrace
  rw [(orderedMatrixSpectrum hH).value_unique sp]

theorem symmetricFunctionTrace_congr {d : ℕ} {H K : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) (he : H = K) (φ : ℝ → ℝ) :
    symmetricFunctionTrace hH φ = symmetricFunctionTrace hK φ := by
  subst K
  rfl

theorem symmetricFunctionTrace_eq_of_diagonalization {d : ℕ}
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian)
    (lam : Fin d → ℝ) (U : Matrix (Fin d) (Fin d) ℝ)
    (hU : Uᵀ * U = 1) (hdiag : Uᵀ * H * U = diagonal lam) (φ : ℝ → ℝ) :
    symmetricFunctionTrace hH φ = ∑ i, φ (lam i) := by
  rw [symmetricFunctionTrace_eq hH (orderedSpectrumOfDiagonalization lam U hU hdiag)]
  exact Equiv.sum_comp (Tuple.sort lam) (fun i => φ (lam i))

theorem symmetricFunctionTrace_isometric_extension {d m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.IsHermitian)
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1) (φ : ℝ → ℝ) (hφ : φ 0 = 0) :
    symmetricFunctionTrace (extension_isHermitian hC B) φ = symmetricFunctionTrace hC φ := by
  have he : (C * Bᵀ) * B = C := by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
  have he' : B * (C * Bᵀ) = B * C * Bᵀ := (Matrix.mul_assoc _ _ _).symm
  have hsmall : ((C * Bᵀ) * B).IsHermitian := by rw [he]; exact hC
  have hlarge : (B * (C * Bᵀ)).IsHermitian := by rw [he']; exact extension_isHermitian hC B
  have h := spectral_sum_rectangular_mul_comm B (C * Bᵀ)
    (orderedMatrixSpectrum hsmall) (orderedMatrixSpectrum hlarge) φ hφ
  change symmetricFunctionTrace hsmall φ = symmetricFunctionTrace hlarge φ at h
  rw [symmetricFunctionTrace_congr hsmall hC he φ,
    symmetricFunctionTrace_congr hlarge (extension_isHermitian hC B) he' φ] at h
  exact h.symm

theorem projectorSandwich_isHermitian {d : ℕ} {H P : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.IsHermitian) (hP : IsOrthogonalProjector P) : (P * H * P).IsHermitian := by
  simpa only [hP.symmetric] using compression_isHermitian hH P

theorem symmetricFunctionTrace_projector_eq_compression {d m : ℕ}
    {H P : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian) (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1) (hBB : B * Bᵀ = P)
    (φ : ℝ → ℝ) (hφ : φ 0 = 0) :
    symmetricFunctionTrace (projectorSandwich_isHermitian hH hP) φ =
      symmetricFunctionTrace (compression_isHermitian hH B) φ := by
  have he : P * H * P = B * (Bᵀ * H * B) * Bᵀ := by
    rw [← hBB]
    simp only [Matrix.mul_assoc]
  exact (symmetricFunctionTrace_congr _ _ he φ).trans
    (symmetricFunctionTrace_isometric_extension (compression_isHermitian hH B) B hB φ hφ)

theorem symmetricFunctionTrace_projector_pinching {d : ℕ}
    {H P : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian) (hP : IsOrthogonalProjector P)
    {φ : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ φ) (hzero : φ 0 = 0) :
    symmetricFunctionTrace (projectorSandwich_isHermitian hH hP) φ +
      symmetricFunctionTrace (projectorSandwich_isHermitian hH hP.complement) φ ≤
        symmetricFunctionTrace hH φ := by
  obtain ⟨B, hB, hBB⟩ := projector_basis_factorization hP rfl
  obtain ⟨k, hd⟩ := Nat.exists_eq_add_of_le' (orthogonal_columns_dimension_le B hB)
  generalize hm : P.rank = m at B hB hBB hd
  subst d
  obtain ⟨C, hC, hCC, hCB⟩ := exists_orthogonal_complement_columns B hB
  rw [hBB] at hCC
  rw [symmetricFunctionTrace_projector_eq_compression hH hP B hB hBB φ hzero,
    symmetricFunctionTrace_projector_eq_compression hH hP.complement C hC hCC φ hzero, add_comm]
  exact convex_complementary_compression_sum_le (orderedMatrixSpectrum hH) C hC B hB hCB
    (orderedMatrixSpectrum (compression_isHermitian hH C))
    (orderedMatrixSpectrum (compression_isHermitian hH B)) hconv (fun _ => Set.mem_univ _)

end
end LowRank
