import LowRank.WeightedSpectralEnergy

/-! Converting weighted subspace error into the actual relative Schatten-2
residual of the algorithm's spectral postprocessing. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

theorem frobeniusSq_spectral_tail_eq_optimum {a m k : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) :
    frobeniusSq (A * sp.basis.submatrix id (Fin.castAdd k)) = optimalSchattenPower 2 A k := by
  have h := ordered_tail_columns_optimal_power (by norm_num : (0 : ℝ) < 2) A sp
  dsimp only at h
  rw [schattenPower_two, frobeniusSq_column_residual A _
    (orthogonal_subcolumns sp.basis sp.orthogonal (Fin.natAdd m) (Fin.natAddEmb m).injective),
    frobeniusSq_spectral_split A sp, add_sub_cancel_right] at h
  exact h

theorem schattenNorm_two_sq {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    schattenNorm 2 A ^ 2 = frobeniusSq A := by
  rw [schattenNorm, ← Real.sqrt_eq_rpow, Real.sq_sqrt (schattenPower_nonneg _ _), schattenPower_two]

theorem optimalSchattenNorm_two_sq {a b k : ℕ} (hk : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ) :
    optimalSchattenNorm 2 A k ^ 2 = optimalSchattenPower 2 A k := by
  have hn : 0 ≤ optimalSchattenPower 2 A k := by
    rw [← optimalColumnSelector_residual_power hk A (by norm_num : (0 : ℝ) < 2)]
    exact schattenPower_nonneg _ _
  rw [optimalSchattenNorm, ← Real.sqrt_eq_rpow, Real.sq_sqrt hn]

theorem schattenNorm_two_relative_of_frobenius {a b k : ℕ} (hk : k ≤ b)
    (A B : Matrix (Fin a) (Fin b) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : frobeniusSq B ≤ (1 + 2 * ε) * optimalSchattenPower 2 A k) :
    schattenNorm 2 B ≤ (1 + ε) * optimalSchattenNorm 2 A k := by
  have hn : 0 ≤ optimalSchattenPower 2 A k := by
    rw [← optimalColumnSelector_residual_power hk A (by norm_num : (0 : ℝ) < 2)]
    exact schattenPower_nonneg _ _
  have hnorm : 0 ≤ optimalSchattenNorm 2 A k := Real.rpow_nonneg hn _
  apply (sq_le_sq₀ (schattenNorm_nonneg _ _) (mul_nonneg (by linarith) hnorm)).mp
  rw [schattenNorm_two_sq, mul_pow, optimalSchattenNorm_two_sq hk]
  exact h.trans (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ε]) hn)

theorem ritz_frobenius_relative_of_weighted_error {a m k : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    {P : Matrix (Fin (m + k)) (Fin (m + k)) ℝ} (hP : IsOrthogonalProjector P)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : frobeniusSq ((1 - P) * (sp.basis.submatrix id (Fin.natAdd m) *
      diagonal (fun j : Fin k => Real.sqrt (sp.value (j.natAdd m))))) ≤
        ε * frobeniusSq (A * sp.basis.submatrix id (Fin.castAdd k))) :
    let Z := optimalColumnSelector a (m + k) k (by omega) (A * P)
    schattenNorm 2 (A * (1 - Z * Zᵀ)) ≤ (1 + ε) * optimalSchattenNorm 2 A k := by
  dsimp only
  apply schattenNorm_two_relative_of_frobenius (by omega) A _ hε
  have hr := ritz_frobenius_residual_le_weighted_error A sp hP
  dsimp only at hr
  rw [frobeniusSq_spectral_tail_eq_optimum A sp] at h hr
  linarith

end
end LowRank
