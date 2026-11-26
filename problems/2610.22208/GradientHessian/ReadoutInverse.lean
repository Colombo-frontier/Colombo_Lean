import GradientHessian.ReadoutSpectral

/-! Actual matrix inverse and the complementary inverse norm required by the
readout certificate, derived from the analytic matrix inequalities. -/

namespace GradientHessian.ReadoutSpectral

open Matrix LowRank
noncomputable section

theorem spectral_inverse_mul {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (hn : ∀ i, sp.value i ≠ 0) :
    (sp.basis * diagonal (fun i => (sp.value i)⁻¹) * sp.basisᵀ) * A = 1 := by
  conv_lhs => rhs; rw [sp.reconstruct]
  calc
    _ = sp.basis * (diagonal (fun i => (sp.value i)⁻¹) *
        (sp.basisᵀ * sp.basis) * diagonal sp.value) * sp.basisᵀ := by noncomm_ring
    _ = sp.basis * (diagonal (fun i => (sp.value i)⁻¹) * diagonal sp.value) * sp.basisᵀ := by
      rw [sp.orthogonal, mul_one]
    _ = 1 := by
      rw [diagonal_mul_diagonal]
      have he : (fun i => (sp.value i)⁻¹ * sp.value i) = fun _ => (1 : ℝ) := by
        funext i; exact inv_mul_cancel₀ (hn i)
      rw [he, diagonal_one, mul_one, sp.orthogonal_right]

theorem spectral_inverse {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum A) (hn : ∀ i, sp.value i ≠ 0) :
    A⁻¹ = sp.basis * diagonal (fun i => (sp.value i)⁻¹) * sp.basisᵀ :=
  Matrix.inv_eq_left_inv (spectral_inverse_mul sp hn)

theorem inverse_bounds {d : ℕ} {A Q : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hQ : IsOrthogonalProjector Q) (hAQ : A * Q = Q)
    (hgap : LoewnerLE (Q + (5 : ℝ) • (1 - Q)) A) {M : ℝ}
    (hupp : LoewnerLE A (M • 1)) :
    A⁻¹ * A = 1 ∧ A⁻¹ * Q = Q ∧ ‖matrixEuclideanMap A⁻¹‖ ≤ 1 ∧
      ‖matrixEuclideanMap (A⁻¹ * (1 - Q))‖ ≤ 1 / 5 := by
  let sp := orderedMatrixSpectrum hA
  obtain ⟨hE, hv⟩ := spectral_projector_and_gap sp hQ hAQ hgap hupp
  have hlow : ∀ i, 1 ≤ sp.value i := by
    intro i; rcases hv i with hi | hi <;> linarith
  have hn : ∀ i, sp.value i ≠ 0 := fun i => ne_of_gt (lt_of_lt_of_le zero_lt_one (hlow i))
  have hInv := spectral_inverse sp hn
  have hI : A⁻¹ * A = 1 := by rw [hInv]; exact spectral_inverse_mul sp hn
  have hIQ : A⁻¹ * Q = Q := by
    calc
      A⁻¹ * Q = A⁻¹ * (A * Q) := by rw [hAQ]
      _ = Q := by rw [← Matrix.mul_assoc, hI, one_mul]
  refine ⟨hI, hIQ, ?_, ?_⟩
  · rw [hInv]
    apply conjugated_diagonal_opNorm_le sp.basis sp.orthogonal _ zero_le_one
    intro i
    rw [abs_of_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one (hlow i)))]
    exact inv_le_one_of_one_le₀ (hlow i)
  · rw [mul_sub, mul_one, hIQ, hInv, ← hE]
    have he : sp.basis * diagonal (fun i => (sp.value i)⁻¹) * sp.basisᵀ - eigenspaceOne sp =
        sp.basis * diagonal (fun i => (sp.value i)⁻¹ - if sp.value i = 1 then 1 else 0) * sp.basisᵀ := by
      rw [eigenspaceOne, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.diagonal_sub]
    rw [he]
    apply conjugated_diagonal_opNorm_le sp.basis sp.orthogonal _ (by norm_num)
    intro i
    rcases hv i with hi | hi
    · simp [hi]
    · have hn1 : sp.value i ≠ 1 := by linarith [hi.1]
      rw [if_neg hn1, sub_zero, abs_of_pos (inv_pos.mpr (by linarith : 0 < sp.value i))]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5) hi.1

end
end GradientHessian.ReadoutSpectral
