import LowRank.SpectralPowers
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Jensen's inequality for the diagonal of an orthogonally transformed
symmetric matrix. Squared change-of-basis coefficients form weights with
both row and column sums equal to one. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem orthogonal_column_square_sum {a b : ℕ} (V : Matrix (Fin a) (Fin b) ℝ)
    (hV : Vᵀ * V = 1) (j : Fin b) : ∑ i, V i j ^ 2 = 1 := by
  have h := congrFun (congrFun hV j) j
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, pow_two] using h

theorem orthogonal_row_square_sum {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ)
    (hV : Vᵀ * V = 1) (i : Fin d) : ∑ j, V i j ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mul_eq_one_comm.mp hV) i) i
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, pow_two] using h

theorem convex_sum_diagonal_le_spectral {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum H) (U : Matrix (Fin d) (Fin d) ℝ) (hU : Uᵀ * U = 1)
    {S : Set ℝ} {φ : ℝ → ℝ} (hφ : ConvexOn ℝ S φ) (hS : ∀ j, sp.value j ∈ S) :
    (∑ i, φ ((Uᵀ * H * U) i i)) ≤ ∑ j, φ (sp.value j) := by
  let C := sp.basisᵀ * U
  have hC : Cᵀ * C = 1 := by
    calc
      _ = Uᵀ * (sp.basis * sp.basisᵀ) * U := by
        simp only [C, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [sp.orthogonal_right, Matrix.mul_one, hU]
  have hcomp : Uᵀ * H * U = Cᵀ * diagonal sp.value * C := by
    calc
      _ = Uᵀ * (sp.basis * diagonal sp.value * sp.basisᵀ) * U := by rw [← sp.reconstruct]
      _ = _ := by simp only [C, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hdiag (i : Fin d) : (Uᵀ * H * U) i i = ∑ j, C j i ^ 2 * sp.value j := by
    rw [hcomp, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    _ ≤ ∑ i, ∑ j, C j i ^ 2 * φ (sp.value j) := by
      apply Finset.sum_le_sum
      intro i _
      rw [hdiag]
      simpa only [smul_eq_mul] using hφ.map_sum_le
        (t := Finset.univ) (w := fun j => C j i ^ 2) (p := sp.value)
        (fun j _ => sq_nonneg _) (orthogonal_column_square_sum C hC i) (fun j _ => hS j)
    _ = ∑ j, φ (sp.value j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, orthogonal_row_square_sum C hC j, one_mul]

theorem diagonal_rpow_sum_le_symmetricPowerTrace {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosSemidef) (U : Matrix (Fin d) (Fin d) ℝ) (hU : Uᵀ * U = 1)
    {r : ℝ} (hr : 1 ≤ r) :
    (∑ i, ((Uᵀ * H * U) i i) ^ r) ≤ symmetricPowerTrace hH.isHermitian r :=
  convex_sum_diagonal_le_spectral (orderedMatrixSpectrum hH.isHermitian) U hU
    (convexOn_rpow hr) (fun j => (orderedMatrixSpectrum hH.isHermitian).value_nonneg hH j)

end
end LowRank
