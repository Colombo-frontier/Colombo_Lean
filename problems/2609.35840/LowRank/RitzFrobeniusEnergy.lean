import LowRank.SpectralRitzColumns
import LowRank.PositiveSpectralLeftColumns

/-! Energy captured by the algorithm's explicit Ritz columns. Zero
compressed eigenvalues need not lie in the query subspace; their original
matrix energy is nonnegative and causes no loss in the comparison. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem frobeniusSq_projector_residual {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    {P : Matrix (Fin b) (Fin b) ℝ} (hP : IsOrthogonalProjector P) :
    frobeniusSq (A * (1 - P)) = frobeniusSq A - frobeniusSq (A * P) := by
  have heq (Q : Matrix (Fin b) (Fin b) ℝ) (hQ : IsOrthogonalProjector Q) :
      frobeniusSq (A * Q) = (A * Q * Aᵀ).trace := by
    rw [frobeniusSq_eq_trace, Matrix.transpose_mul, hQ.symmetric]
    congr 1
    calc
      _ = A * (Q * Q) * Aᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ.idempotent]
  rw [heq _ hP.complement, heq _ hP, Matrix.mul_sub, Matrix.mul_one,
    Matrix.sub_mul, Matrix.trace_sub, ← frobeniusSq_eq_trace]

theorem frobeniusSq_column_residual {a b k : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (Z : Matrix (Fin b) (Fin k) ℝ) (hZ : Zᵀ * Z = 1) :
    frobeniusSq (A * (1 - Z * Zᵀ)) = frobeniusSq A - frobeniusSq (A * Z) := by
  rw [frobeniusSq_projector_residual A (column_projector Z hZ)]
  congr 1
  rw [frobeniusSq_eq_trace, frobeniusSq_eq_trace]
  congr 1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Zᵀ Z, hZ, Matrix.one_mul]

theorem optimalColumnSelector_residual_power {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {p : ℝ} (hp : 0 < p) :
    schattenPower p (A * (1 - optimalColumnSelector a b k hk A * (optimalColumnSelector a b k hk A)ᵀ)) =
      optimalSchattenPower p A k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simpa only [optimalColumnSelector, lastColumnIndex_add] using
    ordered_tail_columns_optimal_power hp A (canonicalOrderedSpectrum (m + k) (symmetricRightGram A))

theorem optimalColumnSelector_captures_max_energy {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (Z : Matrix (Fin b) (Fin k) ℝ) (hZ : Zᵀ * Z = 1) :
    frobeniusSq (A * Z) ≤ frobeniusSq (A * optimalColumnSelector a b k hk A) := by
  have h := optimalSchattenPower_le_rankBounded (by norm_num : (0 : ℝ) < 2) A hk
    (column_projector Z hZ) (le_of_eq (column_projector_rank Z hZ))
  rw [← optimalColumnSelector_residual_power hk A (by norm_num : (0 : ℝ) < 2),
    schattenPower_two, schattenPower_two, frobeniusSq_column_residual A Z hZ,
    frobeniusSq_column_residual A _ (optimalColumnSelector_orthogonal hk A)] at h
  linarith

theorem optimalColumnSelector_column_energy {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (j : Fin k) :
    (∑ i, (A * optimalColumnSelector a b k hk A) i j ^ 2) =
      (canonicalOrderedSpectrum b (symmetricRightGram A)).value (lastColumnIndex b k hk j) := by
  have h := spectral_subcolumns_gram A (canonicalOrderedSpectrum b (symmetricRightGram A))
    (lastColumnIndex b k hk) (lastColumnIndex_injective b k hk)
  have hj := congrFun (congrFun h j) j
  simpa only [optimalColumnSelector, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply_eq, pow_two] using hj

theorem optimalColumnSelector_compressed_energy_le {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ} (hP : IsOrthogonalProjector P) :
    frobeniusSq ((A * P) * optimalColumnSelector a b k hk (A * P)) ≤
      frobeniusSq (A * optimalColumnSelector a b k hk (A * P)) := by
  let Z := optimalColumnSelector a b k hk (A * P)
  change frobeniusSq ((A * P) * Z) ≤ frobeniusSq (A * Z)
  simp only [frobeniusSq]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : (canonicalOrderedSpectrum b (symmetricRightGram (A * P))).value
      (lastColumnIndex b k hk j) = 0
  · rw [show (∑ i, ((A * P) * Z) i j ^ 2) = 0 from
      (optimalColumnSelector_column_energy hk (A * P) j).trans hj]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · have hfix := optimalColumnSelector_compressed_column_fixed hk A hP j hj
    have heq (i : Fin a) : ((A * P) * Z) i j = (A * Z) i j := by
      have h := congrFun (congrArg (fun x => A *ᵥ x) hfix) i
      dsimp only at h
      rw [Matrix.mulVec_mulVec] at h
      exact h
    simp only [heq, le_refl]

theorem ritz_residual_le_of_candidate {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {P : Matrix (Fin b) (Fin b) ℝ} (hP : IsOrthogonalProjector P)
    (V : Matrix (Fin b) (Fin k) ℝ) (hV : Vᵀ * V = 1) :
    let Z := optimalColumnSelector a b k hk (A * P)
    frobeniusSq (A * (1 - Z * Zᵀ)) ≤ frobeniusSq A - frobeniusSq ((A * P) * V) := by
  dsimp only
  rw [frobeniusSq_column_residual A _ (optimalColumnSelector_orthogonal hk (A * P))]
  exact sub_le_sub_left ((optimalColumnSelector_captures_max_energy hk (A * P) V hV).trans
    (optimalColumnSelector_compressed_energy_le hk A hP)) _

end
end LowRank
