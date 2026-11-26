import LowRank.IsometricSpectrum

/-! The actual Schatten residual H(I-P) is the power sum of the Gram
compression to the orthogonal complement of P. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem symmetricPowerTrace_congr {d : ℕ} {A C : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) (heq : A = C) (r : ℝ) :
    symmetricPowerTrace hA r = symmetricPowerTrace hC r := by
  subst C
  rfl

theorem residual_gram_factorization {d t m : ℕ}
    (H : Matrix (Fin d) (Fin t) ℝ) {P : Matrix (Fin t) (Fin t) ℝ}
    (B : Matrix (Fin t) (Fin m) ℝ) (hQ : B * Bᵀ = 1 - P) :
    (H * (1 - P))ᵀ * (H * (1 - P)) = B * (Bᵀ * (Hᵀ * H) * B) * Bᵀ := by
  rw [← hQ]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem schattenPower_residual_eq_compression {d k m : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) {P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ}
    (B : Matrix (Fin (k + m)) (Fin m) ℝ) (hB : Bᵀ * B = 1) (hQ : B * Bᵀ = 1 - P) :
    schattenPower p (H * (1 - P)) =
      symmetricPowerTrace (compression_isHermitian (rightGram_posSemidef H).isHermitian B) (p / 2) := by
  rw [schattenPower_eq_symmetricPowerTrace]
  exact (symmetricPowerTrace_congr _ _ (residual_gram_factorization H B hQ) _).trans
    (symmetricPowerTrace_isometric_extension _ B hB (by positivity))

theorem schattenPower_residual_ge_bottom {d k m : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) {P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ}
    (hP : IsOrthogonalProjector P) (hrank : P.rank = k) :
    bottomPowerTrace (rightGram_posSemidef H).isHermitian m (by omega) (p / 2) ≤
      schattenPower p (H * (1 - P)) := by
  obtain ⟨B, hB, hQ⟩ := projector_complement_basis hP hrank
  rw [schattenPower_residual_eq_compression hp H B hB hQ]
  exact compression_power_ge_bottom (by omega) (rightGram_posSemidef H) B hB (by positivity)

theorem schattenPower_bottom_isLeast {d k m : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) :
    IsLeast {z : ℝ | ∃ P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ,
      IsOrthogonalProjector P ∧ P.rank = k ∧ z = schattenPower p (H * (1 - P))}
      (bottomPowerTrace (rightGram_posSemidef H).isHermitian m (by omega) (p / 2)) := by
  let B := firstEigenvectors (rightGram_posSemidef H).isHermitian (show m ≤ k + m by omega)
  have hB : Bᵀ * B = 1 := firstEigenvectors_orthogonal _ _
  have hP := (column_projector B hB).complement
  have hrank : (1 - B * Bᵀ).rank = k := by
    have h := projector_rank_complement (column_projector B hB)
    rw [column_projector_rank B hB] at h
    omega
  constructor
  · refine ⟨1 - B * Bᵀ, hP, hrank, ?_⟩
    rw [schattenPower_residual_eq_compression hp H B hB (by abel)]
    exact (firstEigenvectors_power _ _ _).symm
  · intro z hz
    obtain ⟨P, hP, hrank, rfl⟩ := hz
    exact schattenPower_residual_ge_bottom hp H hP hrank

end
end LowRank
