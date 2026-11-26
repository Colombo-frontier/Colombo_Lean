import LowRank.FinBlockMatrices
import LowRank.HermitianAbsoluteTrace
import LowRank.SchattenTranspose

/-! The symmetric dilation of a rectangular matrix has absolute spectral
power twice its Schatten power. Block projectors encode independent left
and right projections of the rectangular matrix. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

def hermitianDilation {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℝ := finBlocks 0 A Aᵀ 0

theorem hermitianDilation_isHermitian {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    (hermitianDilation A).IsHermitian := by
  change (hermitianDilation A)ᴴ = hermitianDilation A
  simp only [conjTranspose_eq_transpose_of_trivial, hermitianDilation, finBlocks_transpose,
    Matrix.transpose_zero, Matrix.transpose_transpose]

theorem hermitianDilation_gram {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    (hermitianDilation A)ᵀ * hermitianDilation A = finBlocks (A * Aᵀ) 0 0 (Aᵀ * A) := by
  simp only [hermitianDilation, finBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_transpose, finBlocks_mul, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero]

theorem hermitianDilation_absPowerTrace {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    {p : ℝ} (hp : 0 < p) :
    symmetricAbsPowerTrace (hermitianDilation_isHermitian A) p = 2 * schattenPower p A := by
  rw [symmetricAbsPowerTrace_eq_schattenPower, schattenPower_eq_symmetricPowerTrace]
  rw [symmetricPowerTrace_congr _
    (finBlocks_diagonal_isHermitian (leftGram_posSemidef A).isHermitian
      (rightGram_posSemidef A).isHermitian) (hermitianDilation_gram A) (p / 2)]
  change symmetricFunctionTrace _ (fun x => x ^ (p / 2)) = _
  rw [symmetricFunctionTrace_finBlocks_diagonal]
  change symmetricPowerTrace (leftGram_posSemidef A).isHermitian (p / 2) +
    symmetricPowerTrace (rightGram_posSemidef A).isHermitian (p / 2) = _
  rw [← schattenPower_eq_leftGram hp, ← schattenPower_eq_symmetricPowerTrace]
  ring

theorem hermitianDilation_sandwich {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    {P : Matrix (Fin a) (Fin a) ℝ} (hP : IsOrthogonalProjector P)
    {Q : Matrix (Fin b) (Fin b) ℝ} (hQ : IsOrthogonalProjector Q) :
    finBlocks P 0 0 Q * hermitianDilation A * finBlocks P 0 0 Q = hermitianDilation (P * A * Q) := by
  simp only [hermitianDilation, finBlocks_mul, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, Matrix.transpose_mul, hP.symmetric, hQ.symmetric, Matrix.mul_assoc]

theorem hermitianDilation_complement_sandwich {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    {P : Matrix (Fin a) (Fin a) ℝ} (hP : IsOrthogonalProjector P)
    {Q : Matrix (Fin b) (Fin b) ℝ} (hQ : IsOrthogonalProjector Q) :
    (1 - finBlocks P 0 0 Q) * hermitianDilation A * (1 - finBlocks P 0 0 Q) =
      hermitianDilation ((1 - P) * A * (1 - Q)) := by
  rw [finBlocks_projector_complement]
  exact hermitianDilation_sandwich A hP.complement hQ.complement

end
end LowRank
