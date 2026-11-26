import LowRank.RitzFrobeniusEnergy

/-! Weighted distances from a Gram eigenspace control the loss of captured
energy after projection. These identities connect subspace approximation
to the original matrix residual of the actual Ritz output. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem frobeniusSq_sub {a b : ℕ} (A B : Matrix (Fin a) (Fin b) ℝ) :
    frobeniusSq (A - B) = frobeniusSq A + frobeniusSq B - 2 * (Aᵀ * B).trace := by
  have he : (Bᵀ * A).trace = (Aᵀ * B).trace := by
    rw [← Matrix.trace_transpose (Bᵀ * A), Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [frobeniusSq_eq_trace_right, Matrix.transpose_sub, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.trace_sub, he]
  ring

theorem frobeniusSq_weighted_projector {b k : ℕ}
    {Q : Matrix (Fin b) (Fin b) ℝ} (hQ : IsOrthogonalProjector Q)
    (V : Matrix (Fin b) (Fin k) ℝ) (c : Fin k → ℝ) :
    frobeniusSq (Q * (V * diagonal c)) =
      (diagonal (fun j => c j ^ 2) * Vᵀ * Q * V).trace := by
  rw [frobeniusSq_eq_trace_right]
  have he : (Q * (V * diagonal c))ᵀ * (Q * (V * diagonal c)) =
      diagonal c * (Vᵀ * Q * V) * diagonal c := by
    simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, hQ.symmetric,
      Matrix.mul_assoc, ← Matrix.mul_assoc Q Q, hQ.idempotent]
  rw [he, Matrix.trace_mul_cycle, Matrix.diagonal_mul_diagonal]
  simp only [pow_two, Matrix.mul_assoc]

theorem spectral_projection_energy_loss {a b k : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (f : Fin k → Fin b)
    {P : Matrix (Fin b) (Fin b) ℝ} (hP : IsOrthogonalProjector P) :
    frobeniusSq (A * sp.basis.submatrix id f) - frobeniusSq ((A * P) * sp.basis.submatrix id f) ≤
      2 * frobeniusSq ((1 - P) * (sp.basis.submatrix id f *
        diagonal (fun j => Real.sqrt (sp.value (f j))))) := by
  let V := sp.basis.submatrix id f
  have hright := spectral_subcolumns_mul sp f
  have hleft : Vᵀ * (Aᵀ * A) = diagonal (fun j => sp.value (f j)) * Vᵀ := by
    have h := congrArg Matrix.transpose hright
    simpa only [V, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose] using h
  have hcross : ((A * V)ᵀ * (A * ((1 - P) * V))).trace =
      frobeniusSq ((1 - P) * (V * diagonal (fun j => Real.sqrt (sp.value (f j))))) := by
    rw [frobeniusSq_weighted_projector hP.complement]
    simp only [Real.sq_sqrt (sp.value_nonneg (rightGram_posSemidef A) _)]
    congr 1
    calc
      _ = (Vᵀ * (Aᵀ * A)) * (1 - P) * V := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hleft]
  have hdecomp : (A * P) * V = A * V - A * ((1 - P) * V) := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_assoc, sub_sub_cancel]
  change frobeniusSq (A * V) - frobeniusSq ((A * P) * V) ≤ _
  rw [hdecomp, frobeniusSq_sub, hcross]
  linarith [frobeniusSq_nonneg (A * ((1 - P) * V))]

theorem frobeniusSq_split_columns {a m k : ℕ} (B : Matrix (Fin a) (Fin (m + k)) ℝ) :
    frobeniusSq B = frobeniusSq (B.submatrix id (Fin.castAdd k)) +
      frobeniusSq (B.submatrix id (Fin.natAdd m)) := by
  simp only [frobeniusSq, Matrix.submatrix_apply, id_eq]
  simp_rw [Fin.sum_univ_add]
  exact Finset.sum_add_distrib

theorem frobeniusSq_spectral_split {a m k : ℕ} (A : Matrix (Fin a) (Fin (m + k)) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) :
    frobeniusSq A = frobeniusSq (A * sp.basis.submatrix id (Fin.castAdd k)) +
      frobeniusSq (A * sp.basis.submatrix id (Fin.natAdd m)) := by
  have he : frobeniusSq (A * sp.basis) = frobeniusSq A := by
    rw [frobeniusSq_eq_trace, Matrix.transpose_mul]
    have hm : A * sp.basis * (sp.basisᵀ * Aᵀ) = A * Aᵀ := by
      calc
        _ = A * (sp.basis * sp.basisᵀ) * Aᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [sp.orthogonal_right, Matrix.mul_one]
    rw [hm, ← frobeniusSq_eq_trace]
  rw [← he, frobeniusSq_split_columns]
  rfl

theorem ritz_frobenius_residual_le_weighted_error {a m k : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    {P : Matrix (Fin (m + k)) (Fin (m + k)) ℝ} (hP : IsOrthogonalProjector P) :
    let Z := optimalColumnSelector a (m + k) k (by omega) (A * P)
    frobeniusSq (A * (1 - Z * Zᵀ)) ≤
      frobeniusSq (A * sp.basis.submatrix id (Fin.castAdd k)) +
        2 * frobeniusSq ((1 - P) * (sp.basis.submatrix id (Fin.natAdd m) *
          diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m))))) := by
  have hV := orthogonal_subcolumns sp.basis sp.orthogonal (Fin.natAdd m) (Fin.natAddEmb m).injective
  have hr := ritz_residual_le_of_candidate (by omega : k ≤ m + k) A hP _ hV
  have he := spectral_projection_energy_loss A sp (Fin.natAdd m) hP
  have hsplit := frobeniusSq_spectral_split A sp
  dsimp only at hr ⊢
  linarith

end
end LowRank
