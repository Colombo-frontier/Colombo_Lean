import LowRank.UpperMatrixInterlacing
import LowRank.SchattenResidual

/-! Isometric embeddings preserve the actual Schatten expression, while
restriction to an orthonormal family of right directions decreases it. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem orthogonal_columns_dimension_le {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1) : m ≤ d := by
  have h := (Matrix.rank_mul_le_right Bᵀ B).trans B.rank_le_height
  simpa only [hB, Matrix.rank_one, Fintype.card_fin] using h

theorem symmetricPowerTrace_isometric_extension_of_le {d m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.IsHermitian)
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ * B = 1)
    {r : ℝ} (hr : 0 < r) :
    symmetricPowerTrace (extension_isHermitian hC B) r = symmetricPowerTrace hC r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (orthogonal_columns_dimension_le B hB)
  exact symmetricPowerTrace_isometric_extension hC B hB hr

theorem schattenPower_eq_of_rightGram_eq {a b t : ℕ} (p : ℝ)
    (X : Matrix (Fin a) (Fin t) ℝ) (Y : Matrix (Fin b) (Fin t) ℝ)
    (h : Xᵀ * X = Yᵀ * Y) : schattenPower p X = schattenPower p Y := by
  rw [schattenPower_eq_symmetricPowerTrace, schattenPower_eq_symmetricPowerTrace]
  exact symmetricPowerTrace_congr _ _ h _

theorem schattenPower_left_isometry {a d t : ℕ} (p : ℝ)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (X : Matrix (Fin d) (Fin t) ℝ) : schattenPower p (L * X) = schattenPower p X := by
  apply schattenPower_eq_of_rightGram_eq
  rw [Matrix.transpose_mul]
  calc
    _ = Xᵀ * (Lᵀ * L) * X := by simp only [Matrix.mul_assoc]
    _ = Xᵀ * X := by rw [hL, Matrix.mul_one]

theorem schattenPower_right_isometry_le {d t m : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (X : Matrix (Fin d) (Fin t) ℝ)
    (B : Matrix (Fin t) (Fin m) ℝ) (hB : Bᵀ * B = 1) :
    schattenPower p (X * B) ≤ schattenPower p X := by
  rw [schattenPower_eq_symmetricPowerTrace, schattenPower_eq_symmetricPowerTrace]
  have hGram : (X * B)ᵀ * (X * B) = Bᵀ * (Xᵀ * X) * B := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [symmetricPowerTrace_congr _ (compression_isHermitian (rightGram_posSemidef X).isHermitian B)
    hGram (p / 2)]
  exact compression_power_le_total (orthogonal_columns_dimension_le B hB)
    (rightGram_posSemidef X) B hB (by positivity)

theorem schattenPower_right_extension {d t m : ℕ} {p : ℝ} (hp : 0 < p)
    (X : Matrix (Fin d) (Fin m) ℝ)
    (B : Matrix (Fin t) (Fin m) ℝ) (hB : Bᵀ * B = 1) :
    schattenPower p (X * Bᵀ) = schattenPower p X := by
  rw [schattenPower_eq_symmetricPowerTrace, schattenPower_eq_symmetricPowerTrace]
  have hGram : (X * Bᵀ)ᵀ * (X * Bᵀ) = B * (Xᵀ * X) * Bᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  exact (symmetricPowerTrace_congr _ _ hGram _).trans
    (symmetricPowerTrace_isometric_extension_of_le (rightGram_posSemidef X).isHermitian B hB
      (by positivity))

theorem schattenPower_isometric_embedding {a b d t : ℕ} {p : ℝ} (hp : 0 < p)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix (Fin b) (Fin t) ℝ) (hR : Rᵀ * R = 1)
    (X : Matrix (Fin d) (Fin t) ℝ) :
    schattenPower p (L * X * Rᵀ) = schattenPower p X := by
  rw [schattenPower_right_extension hp _ R hR, schattenPower_left_isometry p L hL]

theorem schattenNorm_isometric_embedding {a b d t : ℕ} {p : ℝ} (hp : 0 < p)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix (Fin b) (Fin t) ℝ) (hR : Rᵀ * R = 1)
    (X : Matrix (Fin d) (Fin t) ℝ) :
    schattenNorm p (L * X * Rᵀ) = schattenNorm p X := by
  simp only [schattenNorm, schattenPower_isometric_embedding hp L hL R hR X]

end
end LowRank
