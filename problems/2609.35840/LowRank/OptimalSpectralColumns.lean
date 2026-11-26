import LowRank.SchattenRankBounded
import LowRank.SchattenTruncation

/-! The last k columns of any ordered Gram eigenbasis attain the true
rank-k Schatten optimum. The proof keeps the chosen basis explicit. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem orthogonal_subcolumns {d t k : ℕ} (U : Matrix (Fin d) (Fin t) ℝ)
    (hU : Uᵀ * U = 1) (f : Fin k → Fin t) (hf : Function.Injective f) :
    (U.submatrix id f)ᵀ * U.submatrix id f = 1 := by
  have h := compressed_submatrix U (1 : Matrix (Fin d) (Fin d) ℝ) f
  simpa only [Matrix.mul_one, hU, Matrix.submatrix_one _ hf] using h

theorem split_columns_projector {d m k : ℕ} (U : Matrix (Fin d) (Fin (m + k)) ℝ) :
    U.submatrix id (Fin.castAdd k) * (U.submatrix id (Fin.castAdd k))ᵀ +
      U.submatrix id (Fin.natAdd m) * (U.submatrix id (Fin.natAdd m))ᵀ = U * Uᵀ := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix, id_eq]
  exact (Fin.sum_univ_add (fun l : Fin (m + k) => U i l * U j l)).symm

theorem ordered_tail_columns_optimal_power {a m k : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Hᵀ * H)) :
    let Z := sp.basis.submatrix id (Fin.natAdd m)
    schattenPower p (H * (1 - Z * Zᵀ)) = optimalSchattenPower p H k := by
  let B := sp.basis.submatrix id (Fin.castAdd k)
  let Z := sp.basis.submatrix id (Fin.natAdd m)
  have hinj : Function.Injective (Fin.castAdd k : Fin m → Fin (m + k)) :=
    fun _ _ h => Fin.ext (congrArg (fun z : Fin (m + k) => z.val) h)
  have hB : Bᵀ * B = 1 := orthogonal_subcolumns _ sp.orthogonal _ hinj
  have hQ : B * Bᵀ = 1 - Z * Zᵀ := by
    apply eq_sub_of_add_eq
    exact (split_columns_projector sp.basis).trans sp.orthogonal_right
  have hdiag : (H * B)ᵀ * (H * B) = diagonal (fun i : Fin m => sp.value (i.castAdd k)) := by
    calc
      _ = Bᵀ * (Hᵀ * H) * B := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by
        change (sp.basis.submatrix id (Fin.castAdd k))ᵀ * (Hᵀ * H) *
          sp.basis.submatrix id (Fin.castAdd k) = _
        rw [compressed_submatrix, sp.diagonalizes, Matrix.submatrix_diagonal _ _ hinj]
        rfl
  let spB : OrderedMatrixSpectrum ((H * B)ᵀ * (H * B)) := {
    value := fun i => sp.value (i.castAdd k)
    basis := 1
    increasing := fun _ _ hij => sp.increasing (by simpa using hij)
    orthogonal := by simp
    diagonalizes := by simpa only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using hdiag }
  change schattenPower p (H * (1 - Z * Zᵀ)) = _
  rw [schattenPower_residual_eq_columns hp H B hB hQ,
    schattenPower_eq_symmetricPowerTrace, symmetricPowerTrace_eq _ spB,
    optimalSchattenPower_eq_bottom_of_le hp H (by omega)]
  simp only [Nat.add_sub_cancel]
  unfold bottomPowerTrace
  rw [(orderedMatrixSpectrum (rightGram_posSemidef H).isHermitian).value_unique sp]
  rfl

theorem ordered_tail_columns_optimal_norm {a m k : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Hᵀ * H)) :
    let Z := sp.basis.submatrix id (Fin.natAdd m)
    schattenNorm p (H * (1 - Z * Zᵀ)) = optimalSchattenNorm p H k := by
  dsimp only
  rw [schattenNorm, optimalSchattenNorm, ordered_tail_columns_optimal_power hp H sp]

end
end LowRank
