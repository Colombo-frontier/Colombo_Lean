import LowRank.CompressedRitzPower

/-! The explicit top spectral selector maximizes captured positive Schatten
power. Enlarging a query subspace therefore preserves the captured-power
guarantee of each smaller compressed candidate, including singular cases. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem lastColumnIndex_eq_rev_castLE_rev {b k : ℕ} (hk : k ≤ b) (j : Fin k) :
    lastColumnIndex b k hk j = (j.rev.castLE hk).rev := by
  apply Fin.ext
  simp only [lastColumnIndex, Fin.val_rev, Fin.coe_castLE]
  omega

theorem orthogonal_columns_eigenvalue_le_top {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (V : Matrix (Fin b) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (spA : OrderedMatrixSpectrum (Aᵀ * A)) (spV : OrderedMatrixSpectrum ((A * V)ᵀ * (A * V)))
    (j : Fin k) : spV.value j ≤ spA.value (lastColumnIndex b k hk j) := by
  rw [lastColumnIndex_eq_rev_castLE_rev]
  exact ordered_compression_eigenvalue_le_upper hk spA spV V hV
    (by simp only [Matrix.transpose_mul, Matrix.mul_assoc]) j

theorem optimalColumnSelector_captures_max_power {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (V : Matrix (Fin b) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    {p : ℝ} (hp : 0 ≤ p) :
    schattenPower p (A * V) ≤ schattenPower p (A * optimalColumnSelector a b k hk A) := by
  rw [optimalColumnSelector_schattenPower, schattenPower_eq_symmetricPowerTrace]
  let spV := orderedMatrixSpectrum (rightGram_posSemidef (A * V)).isHermitian
  rw [symmetricPowerTrace_eq _ spV]
  apply Finset.sum_le_sum
  intro j _
  exact Real.rpow_le_rpow (spV.value_nonneg (rightGram_posSemidef _) j)
    (orthogonal_columns_eigenvalue_le_top hk A V hV
      (canonicalOrderedSpectrum b (symmetricRightGram A)) spV j) (by positivity)

theorem compressedRitz_captures_candidate_power {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ}
    (hP : IsOrthogonalProjector P) (V : Matrix (Fin b) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    {p : ℝ} (hp : 0 < p) :
    schattenPower p ((A * P) * V) ≤
      schattenPower p (A * optimalColumnSelector a b k hk (A * P)) :=
  (optimalColumnSelector_captures_max_power hk (A * P) V hV hp.le).trans
    (optimalColumnSelector_compressed_power_le hk A hP hp)

theorem compressedRitz_captures_supported_power {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ}
    (hP : IsOrthogonalProjector P) (V : Matrix (Fin b) (Fin k) ℝ)
    (hV : Vᵀ * V = 1) (hPV : P * V = V) {p : ℝ} (hp : 0 < p) :
    schattenPower p (A * V) ≤
      schattenPower p (A * optimalColumnSelector a b k hk (A * P)) := by
  have h := compressedRitz_captures_candidate_power hk A hP V hV hp
  rwa [Matrix.mul_assoc, hPV] at h

theorem compressedRitz_power_mono_subspace {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P Q : Matrix (Fin b) (Fin b) ℝ}
    (hQ : IsOrthogonalProjector Q) (hPQ : P * Q = Q) {p : ℝ} (hp : 0 < p) :
    schattenPower p ((A * Q) * optimalColumnSelector a b k hk (A * Q)) ≤
      schattenPower p ((A * P) * optimalColumnSelector a b k hk (A * P)) := by
  have he : (A * P) * Q = A * Q := by rw [Matrix.mul_assoc, hPQ]
  have h := optimalColumnSelector_compressed_power_le hk (A * P) hQ hp
  rw [he] at h
  exact h.trans (optimalColumnSelector_captures_max_power hk (A * P) _
    (optimalColumnSelector_orthogonal hk (A * Q)) hp.le)

theorem compressedRitz_captures_subspace_power {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P Q : Matrix (Fin b) (Fin b) ℝ}
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (hPQ : P * Q = Q) {p : ℝ} (hp : 0 < p) :
    schattenPower p ((A * Q) * optimalColumnSelector a b k hk (A * Q)) ≤
      schattenPower p (A * optimalColumnSelector a b k hk (A * P)) :=
  (compressedRitz_power_mono_subspace hk A hQ hPQ hp).trans
    (optimalColumnSelector_compressed_power_le hk A hP hp)

end
end LowRank
