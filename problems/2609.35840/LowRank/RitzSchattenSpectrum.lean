import LowRank.RitzFrobeniusEnergy

/-! Exact Schatten power sums of the measurable spectral selector and
their transfer from a compressed matrix when its selected directions
belong to the query subspace. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem lastColumnIndex_monotone (b k : ℕ) (hk : k ≤ b) : Monotone (lastColumnIndex b k hk) := by
  intro i j hij
  change b - k + i.val ≤ b - k + j.val
  exact Nat.add_le_add_left hij _

theorem optimalColumnSelector_gram {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) :
    (A * optimalColumnSelector a b k hk A)ᵀ * (A * optimalColumnSelector a b k hk A) =
      diagonal (fun j => (canonicalOrderedSpectrum b (symmetricRightGram A)).value
        (lastColumnIndex b k hk j)) :=
  spectral_subcolumns_gram A (canonicalOrderedSpectrum b (symmetricRightGram A))
    (lastColumnIndex b k hk) (lastColumnIndex_injective b k hk)

theorem optimalColumnSelector_schattenPower {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (p : ℝ) :
    schattenPower p (A * optimalColumnSelector a b k hk A) =
      ∑ j, ((canonicalOrderedSpectrum b (symmetricRightGram A)).value
        (lastColumnIndex b k hk j)) ^ (p / 2) := by
  let sp := canonicalOrderedSpectrum b (symmetricRightGram A)
  let spZ : OrderedMatrixSpectrum
      ((A * optimalColumnSelector a b k hk A)ᵀ * (A * optimalColumnSelector a b k hk A)) := {
    value := fun j => sp.value (lastColumnIndex b k hk j)
    basis := 1
    increasing := sp.increasing.comp (lastColumnIndex_monotone b k hk)
    orthogonal := by simp
    diagonalizes := by
      simpa only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using optimalColumnSelector_gram hk A }
  rw [schattenPower_eq_symmetricPowerTrace, symmetricPowerTrace_eq _ spZ]

theorem optimalColumnSelector_schattenPower_eq_column_sum {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (p : ℝ) :
    schattenPower p (A * optimalColumnSelector a b k hk A) =
      ∑ j, (∑ i, (A * optimalColumnSelector a b k hk A) i j ^ 2) ^ (p / 2) := by
  simp_rw [optimalColumnSelector_column_energy]
  exact optimalColumnSelector_schattenPower hk A p

theorem optimalColumnSelector_compressed_fixed {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ} (hP : IsOrthogonalProjector P)
    (hn : ∀ j, (canonicalOrderedSpectrum b (symmetricRightGram (A * P))).value
      (lastColumnIndex b k hk j) ≠ 0) :
    P * optimalColumnSelector a b k hk (A * P) = optimalColumnSelector a b k hk (A * P) := by
  ext i j
  exact congrFun (optimalColumnSelector_compressed_column_fixed hk A hP j (hn j)) i

theorem optimalColumnSelector_compressed_schattenPower {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ}
    (hfix : P * optimalColumnSelector a b k hk (A * P) = optimalColumnSelector a b k hk (A * P))
    (p : ℝ) :
    schattenPower p (A * optimalColumnSelector a b k hk (A * P)) =
      ∑ j, ((canonicalOrderedSpectrum b (symmetricRightGram (A * P))).value
        (lastColumnIndex b k hk j)) ^ (p / 2) := by
  have he : (A * P) * optimalColumnSelector a b k hk (A * P) =
      A * optimalColumnSelector a b k hk (A * P) := by rw [Matrix.mul_assoc, hfix]
  rw [← he]
  exact optimalColumnSelector_schattenPower hk (A * P) p

end
end LowRank
