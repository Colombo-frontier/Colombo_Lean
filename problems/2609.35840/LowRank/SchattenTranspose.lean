import LowRank.SpectralTraceInterchange
import LowRank.SchattenIsometry

/-! Transposition preserves every positive Schatten power, with all extra
zero singular values handled by the rectangular spectral trace identity. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem leftGram_posSemidef {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    (A * Aᵀ).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose A

theorem schattenPower_eq_leftGram {a b : ℕ} {p : ℝ} (hp : 0 < p)
    (A : Matrix (Fin a) (Fin b) ℝ) :
    schattenPower p A = symmetricPowerTrace (leftGram_posSemidef A).isHermitian (p / 2) := by
  rw [schattenPower_eq_symmetricPowerTrace]
  exact spectral_sum_rectangular_mul_comm A Aᵀ
    (orderedMatrixSpectrum (rightGram_posSemidef A).isHermitian)
    (orderedMatrixSpectrum (leftGram_posSemidef A).isHermitian)
    (fun x => x ^ (p / 2)) (Real.zero_rpow (by positivity))

theorem schattenPower_transpose {a b : ℕ} {p : ℝ} (hp : 0 < p)
    (A : Matrix (Fin a) (Fin b) ℝ) : schattenPower p Aᵀ = schattenPower p A := by
  rw [schattenPower_eq_symmetricPowerTrace, schattenPower_eq_leftGram hp A]

theorem schattenNorm_transpose {a b : ℕ} {p : ℝ} (hp : 0 < p)
    (A : Matrix (Fin a) (Fin b) ℝ) : schattenNorm p Aᵀ = schattenNorm p A := by
  rw [schattenNorm, schattenNorm, schattenPower_transpose hp]

theorem schattenPower_eq_of_leftGram_eq {a b c : ℕ} {p : ℝ} (hp : 0 < p)
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin a) (Fin c) ℝ)
    (he : A * Aᵀ = B * Bᵀ) : schattenPower p A = schattenPower p B := by
  rw [schattenPower_eq_leftGram hp, schattenPower_eq_leftGram hp]
  exact symmetricPowerTrace_congr _ _ he _

end
end LowRank
