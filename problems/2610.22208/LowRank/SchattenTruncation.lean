import LowRank.SchattenIsometry
import LowRank.ColumnRangeProjector

/-! Truncate the output columns of an isometrically embedded matrix and
project onto their span. The resulting rank bound and Schatten error
comparison hold even when the truncated columns are linearly dependent. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

theorem schattenPower_residual_eq_columns {d t m : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin t) ℝ) {P : Matrix (Fin t) (Fin t) ℝ}
    (B : Matrix (Fin t) (Fin m) ℝ) (hB : Bᵀ * B = 1) (hQ : B * Bᵀ = 1 - P) :
    schattenPower p (H * (1 - P)) = schattenPower p (H * B) := by
  rw [← hQ, ← Matrix.mul_assoc]
  exact schattenPower_right_extension hp _ B hB

theorem projector_mul_complement_columns {d m : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1) (hQ : B * Bᵀ = 1 - P) :
    P * B = 0 := by
  have hPB : P = 1 - B * Bᵀ := by rw [hQ]; abel
  rw [hPB, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hB, Matrix.mul_one, sub_self]

theorem schattenPower_truncated_residual_le {a b d t k : ℕ} {p : ℝ} (hp : 0 < p)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix (Fin b) (Fin t) ℝ) (hR : Rᵀ * R = 1)
    (A : Matrix (Fin d) (Fin t) ℝ) (Z : Matrix (Fin b) (Fin k) ℝ)
    {P : Matrix (Fin t) (Fin t) ℝ} (hP : IsOrthogonalProjector P)
    (hs : P * (Rᵀ * Z) = Rᵀ * Z) :
    schattenPower p (A * (1 - P)) ≤
      schattenPower p (L * A * Rᵀ * (1 - Z * Zᵀ)) := by
  obtain ⟨B, hB, hQ⟩ := projector_basis_factorization hP.complement rfl
  have hPB := projector_mul_complement_columns B hB hQ
  have hs' : Zᵀ * R * P = Zᵀ * R := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hP.symmetric]
      using congrArg Matrix.transpose hs
  have hZB : Zᵀ * R * B = 0 := by
    calc
      _ = (Zᵀ * R * P) * B := by rw [hs']
      _ = 0 := by rw [Matrix.mul_assoc, hPB, Matrix.mul_zero]
  have hRB : (R * B)ᵀ * (R * B) = 1 := by
    rw [Matrix.transpose_mul]
    calc
      _ = Bᵀ * (Rᵀ * R) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hR, Matrix.mul_one, hB]
  have hres : (L * A * Rᵀ * (1 - Z * Zᵀ)) * (R * B) = L * (A * B) := by
    calc
      _ = L * A * (Rᵀ * R) * B - L * A * Rᵀ * Z * (Zᵀ * R * B) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      _ = _ := by rw [hR, Matrix.mul_one, hZB, Matrix.mul_zero, sub_zero, Matrix.mul_assoc]
  calc
    _ = schattenPower p (A * B) := schattenPower_residual_eq_columns hp A B hB hQ
    _ = schattenPower p (L * (A * B)) := (schattenPower_left_isometry p L hL _).symm
    _ = schattenPower p ((L * A * Rᵀ * (1 - Z * Zᵀ)) * (R * B)) := by rw [hres]
    _ ≤ _ := schattenPower_right_isometry_le hp.le _ _ hRB

def truncatedColumnProjector {b t k : ℕ}
    (R : Matrix (Fin b) (Fin t) ℝ) (Z : Matrix (Fin b) (Fin k) ℝ) :
    Matrix (Fin t) (Fin t) ℝ := columnRangeProjector (Rᵀ * Z)

theorem truncatedColumnProjector_spec {b t k : ℕ}
    (R : Matrix (Fin b) (Fin t) ℝ) (Z : Matrix (Fin b) (Fin k) ℝ) :
    IsOrthogonalProjector (truncatedColumnProjector R Z) ∧
      (truncatedColumnProjector R Z).rank ≤ k ∧
      truncatedColumnProjector R Z * (Rᵀ * Z) = Rᵀ * Z :=
  ⟨columnRangeProjector_isProjector _, columnRangeProjector_rank_le _, columnRangeProjector_fixes _⟩

theorem schattenNorm_truncatedColumnProjector_le {a b d t k : ℕ} {p : ℝ} (hp : 0 < p)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix (Fin b) (Fin t) ℝ) (hR : Rᵀ * R = 1)
    (A : Matrix (Fin d) (Fin t) ℝ) (Z : Matrix (Fin b) (Fin k) ℝ) :
    schattenNorm p (A * (1 - truncatedColumnProjector R Z)) ≤
      schattenNorm p (L * A * Rᵀ * (1 - Z * Zᵀ)) := by
  obtain ⟨hP, _, hs⟩ := truncatedColumnProjector_spec R Z
  exact Real.rpow_le_rpow (schattenPower_nonneg _ _)
    (schattenPower_truncated_residual_le hp L hL R hR A Z hP hs) (by positivity)

theorem measurable_truncatedColumnProjector {b t k : ℕ}
    (R : Matrix (Fin b) (Fin t) ℝ) :
    Measurable (truncatedColumnProjector R : Matrix (Fin b) (Fin k) ℝ →
      Matrix (Fin t) (Fin t) ℝ) := by
  have h : Continuous (fun Z : Matrix (Fin b) (Fin k) ℝ => Rᵀ * Z) := by fun_prop
  exact (measurable_columnRangeProjector t k).comp h.measurable

end
end LowRank
