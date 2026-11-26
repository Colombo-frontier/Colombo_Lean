import LowRank.SchattenTranspose
import LowRank.RitzSchattenResidual

/-! Transposition preserves the attained rank-k Schatten optimum. The
proof transports any optimal right subspace through the matrix and uses
the rank-at-most-k variational characterization, including rank deficiency. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

theorem optimalSchattenPower_transpose_le {a b k : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {p : ℝ} (hp : 0 < p) :
    optimalSchattenPower p Aᵀ k ≤ optimalSchattenPower p A k := by
  let Z := optimalColumnSelector a b k hkb A
  let Q := columnRangeProjector (A * Z)
  have hQ : IsOrthogonalProjector Q := columnRangeProjector_isProjector (A * Z)
  have hfix : Q * (A * Z) = A * Z := columnRangeProjector_fixes _
  have hz : (1 - Q) * (A * Z) = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hfix, sub_self]
  have hres : (1 - Q) * (A * (1 - Z * Zᵀ)) = (1 - Q) * A := by
    calc
      _ = (1 - Q) * A - ((1 - Q) * (A * Z)) * Zᵀ := by
        simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hz, Matrix.zero_mul, sub_zero]
  calc
    _ ≤ schattenPower p (Aᵀ * (1 - Q)) :=
      optimalSchattenPower_le_rankBounded hp Aᵀ hka hQ (columnRangeProjector_rank_le _)
    _ = schattenPower p ((1 - Q) * A) := by
      rw [← schattenPower_transpose hp ((1 - Q) * A)]
      simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hQ.symmetric]
    _ = schattenPower p ((1 - Q) * (A * (1 - Z * Zᵀ))) := by rw [hres]
    _ ≤ schattenPower p (A * (1 - Z * Zᵀ)) := schattenPower_left_projector_le hp.le _ hQ.complement
    _ = _ := optimalColumnSelector_residual_power hkb A hp

theorem optimalSchattenPower_transpose {a b k : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {p : ℝ} (hp : 0 < p) :
    optimalSchattenPower p Aᵀ k = optimalSchattenPower p A k := by
  apply le_antisymm (optimalSchattenPower_transpose_le hka hkb A hp)
  simpa only [Matrix.transpose_transpose] using optimalSchattenPower_transpose_le hkb hka Aᵀ hp

theorem optimalSchattenNorm_transpose {a b k : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {p : ℝ} (hp : 0 < p) :
    optimalSchattenNorm p Aᵀ k = optimalSchattenNorm p A k := by
  rw [optimalSchattenNorm, optimalSchattenNorm, optimalSchattenPower_transpose hka hkb A hp]

theorem optimalColumnSelector_capture_transpose {a b k : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {p : ℝ} (hp : 0 < p) :
    schattenPower p (Aᵀ * optimalColumnSelector b a k hka Aᵀ) =
      schattenPower p (A * optimalColumnSelector a b k hkb A) := by
  have hl := schattenPower_eq_optimum_add_capture hka Aᵀ hp
  have hr := schattenPower_eq_optimum_add_capture hkb A hp
  rw [schattenPower_transpose hp, optimalSchattenPower_transpose hka hkb A hp] at hl
  linarith

end
end LowRank
