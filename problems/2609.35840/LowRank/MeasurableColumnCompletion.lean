import LowRank.RitzFrobeniusEnergy
import LowRank.SchattenExactRecovery
import LowRank.ColumnRangeProjector

/-! Complete any k-column matrix to an orthonormal k-column output whose
projector contains its range. This total measurable map handles zero and
dependent input columns without requiring a rank test from the caller. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def completeOrthonormalColumns (b k : ℕ) (hk : k ≤ b) (B : Matrix (Fin b) (Fin k) ℝ) :
    Matrix (Fin b) (Fin k) ℝ := optimalColumnSelector b b k hk (columnRangeProjector B)

theorem completeOrthonormalColumns_orthogonal {b k : ℕ} (hk : k ≤ b)
    (B : Matrix (Fin b) (Fin k) ℝ) :
    (completeOrthonormalColumns b k hk B)ᵀ * completeOrthonormalColumns b k hk B = 1 :=
  optimalColumnSelector_orthogonal hk _

theorem measurable_completeOrthonormalColumns (b k : ℕ) (hk : k ≤ b) :
    Measurable (completeOrthonormalColumns b k hk) :=
  (measurable_optimalColumnSelector b b k hk).comp (measurable_columnRangeProjector b k)

theorem completeOrthonormalColumns_fixes {b k : ℕ} (hk : k ≤ b)
    (B : Matrix (Fin b) (Fin k) ℝ) :
    (completeOrthonormalColumns b k hk B * (completeOrthonormalColumns b k hk B)ᵀ) * B = B := by
  let Q := columnRangeProjector B
  let Z := completeOrthonormalColumns b k hk B
  have hQ : IsOrthogonalProjector Q := columnRangeProjector_isProjector B
  have hz : Q * (1 - Q) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hQ.idempotent, sub_self]
  have ho := optimalSchattenPower_le_rankBounded (by norm_num : (0 : ℝ) < 2) Q hk hQ
    (columnRangeProjector_rank_le B)
  rw [hz, schattenPower_two, show frobeniusSq (0 : Matrix (Fin b) (Fin b) ℝ) = 0 by simp [frobeniusSq]] at ho
  have hr : frobeniusSq (Q * (1 - Z * Zᵀ)) = 0 := by
    apply le_antisymm _ (frobeniusSq_nonneg _)
    rw [← schattenPower_two]
    change schattenPower 2 (Q * (1 - optimalColumnSelector b b k hk Q *
      (optimalColumnSelector b b k hk Q)ᵀ)) ≤ 0
    rw [optimalColumnSelector_residual_power hk Q (by norm_num : (0 : ℝ) < 2)]
    exact ho
  have hres := (frobeniusSq_eq_zero_iff _).mp hr
  have hres' : (1 - Z * Zᵀ) * Q = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_transpose, hQ.symmetric, Matrix.transpose_zero] using congrArg Matrix.transpose hres
  have hZQ : Z * Zᵀ * Q = Q := by
    rw [Matrix.sub_mul, Matrix.one_mul] at hres'
    exact (sub_eq_zero.mp hres').symm
  change (Z * Zᵀ) * B = B
  calc
    _ = (Z * Zᵀ) * (Q * B) := by rw [columnRangeProjector_fixes]
    _ = B := by rw [← Matrix.mul_assoc, hZQ, columnRangeProjector_fixes]

end
end LowRank
