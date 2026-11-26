import LowRank.MeasurableColumnCompletion
import LowRank.SchattenTransposeOptimum

/-! Convert a left subspace into a right output using its image under the
transpose. The residual cannot increase, including rank-deficient images. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem transpose_output_residual_power_le {a b k : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (Z : Matrix (Fin a) (Fin k) ℝ)
    {Q : Matrix (Fin b) (Fin b) ℝ} (hQ : IsOrthogonalProjector Q)
    (hfix : Q * (Aᵀ * Z) = Aᵀ * Z) {p : ℝ} (hp : 0 < p) :
    schattenPower p (A * (1 - Q)) ≤ schattenPower p (Aᵀ * (1 - Z * Zᵀ)) := by
  have hz : (1 - Q) * (Aᵀ * Z) = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hfix, sub_self]
  have hzt : (Zᵀ * A) * (1 - Q) = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_transpose, hQ.symmetric, Matrix.transpose_zero] using congrArg Matrix.transpose hz
  have hres : ((1 - Z * Zᵀ) * A) * (1 - Q) = A * (1 - Q) := by
    calc
      _ = A * (1 - Q) - Z * ((Zᵀ * A) * (1 - Q)) := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = _ := by rw [hzt, Matrix.mul_zero, sub_zero]
  calc
    _ = schattenPower p (((1 - Z * Zᵀ) * A) * (1 - Q)) := by rw [hres]
    _ ≤ schattenPower p ((1 - Z * Zᵀ) * A) := schattenPower_right_projector_le hp _ hQ.complement
    _ = _ := by
      rw [← schattenPower_transpose hp ((1 - Z * Zᵀ) * A)]
      simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose]

theorem completeTransposeImage_residual_le {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (Z : Matrix (Fin a) (Fin k) ℝ) {p : ℝ} (hp : 0 < p) :
    let Y := completeOrthonormalColumns b k hk (Aᵀ * Z)
    schattenNorm p (A * (1 - Y * Yᵀ)) ≤ schattenNorm p (Aᵀ * (1 - Z * Zᵀ)) := by
  dsimp only
  apply Real.rpow_le_rpow (schattenPower_nonneg _ _) _ (by positivity : 0 ≤ 1 / p)
  exact transpose_output_residual_power_le A Z
    (column_projector _ (completeOrthonormalColumns_orthogonal hk _))
    (completeOrthonormalColumns_fixes hk _) hp

theorem completeTransposeImage_relative {a b k : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) (Z : Matrix (Fin a) (Fin k) ℝ) {p ε : ℝ} (hp : 0 < p)
    (h : schattenNorm p (Aᵀ * (1 - Z * Zᵀ)) ≤ (1 + ε) * optimalSchattenNorm p Aᵀ k) :
    let Y := completeOrthonormalColumns b k hkb (Aᵀ * Z)
    schattenNorm p (A * (1 - Y * Yᵀ)) ≤ (1 + ε) * optimalSchattenNorm p A k := by
  rw [optimalSchattenNorm_transpose hka hkb A hp] at h
  exact (completeTransposeImage_residual_le hkb A Z hp).trans h

end
end LowRank
