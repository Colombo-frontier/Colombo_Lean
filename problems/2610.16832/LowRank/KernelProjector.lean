import LowRank.BlockKernel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! An explicit left-kernel projector for a full-column-rank real matrix.
The formula is total: on singular Gram matrices the inverse convention makes
it the identity. It remains an orthogonal projector everywhere. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def leftKernelProjector (D : Matrix m n ℝ) : Matrix m m ℝ :=
  1 - D * (Dᵀ * D)⁻¹ * Dᵀ

theorem gram_det_isUnit_of_injective (D : Matrix m n ℝ) (hD : Function.Injective D.mulVec) :
    IsUnit (Dᵀ * D).det := by
  have hk : LinearMap.ker (Dᵀ * D).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot.mpr hD
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hk))

theorem leftKernelProjector_isProjector (D : Matrix m n ℝ) :
    IsOrthogonalProjector (leftKernelProjector D) := by
  have hs : (D * (Dᵀ * D)⁻¹ * Dᵀ)ᵀ = D * (Dᵀ * D)⁻¹ * Dᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
      Matrix.mul_assoc]
  have hi : (D * (Dᵀ * D)⁻¹ * Dᵀ) * (D * (Dᵀ * D)⁻¹ * Dᵀ) =
      D * (Dᵀ * D)⁻¹ * Dᵀ := by
    rcases Matrix.nonsing_inv_cancel_or_zero (Dᵀ * D) with h | h
    · calc
        _ = D * ((Dᵀ * D)⁻¹ * (Dᵀ * D)) * (Dᵀ * D)⁻¹ * Dᵀ := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [h.1, Matrix.mul_one]
    · simp [h]
  exact (IsOrthogonalProjector.mk hs hi).complement

theorem transpose_mul_leftKernelProjector (D : Matrix m n ℝ) (hD : Function.Injective D.mulVec) :
    Dᵀ * leftKernelProjector D = 0 := by
  have hc : Dᵀ * (D * (Dᵀ * D)⁻¹ * Dᵀ) = Dᵀ := by
    calc
      _ = ((Dᵀ * D) * (Dᵀ * D)⁻¹) * Dᵀ := by simp only [Matrix.mul_assoc]
      _ = Dᵀ := by rw [Matrix.mul_nonsing_inv _ (gram_det_isUnit_of_injective D hD), Matrix.one_mul]
  simp only [leftKernelProjector, Matrix.mul_sub, Matrix.mul_one, hc, sub_self]

theorem leftKernelProjector_fixed_iff (D : Matrix m n ℝ) (hD : Function.Injective D.mulVec)
    (x : m → ℝ) : leftKernelProjector D *ᵥ x = x ↔ Dᵀ *ᵥ x = 0 := by
  constructor
  · intro hx
    rw [← hx, Matrix.mulVec_mulVec, transpose_mul_leftKernelProjector D hD, Matrix.zero_mulVec]
  · intro hx
    simp only [leftKernelProjector, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      hx, Matrix.mulVec_zero, sub_zero]

theorem leftKernelProjector_range (D : Matrix m n ℝ) (hD : Function.Injective D.mulVec) :
    LinearMap.range (leftKernelProjector D).mulVecLin = LinearMap.ker Dᵀ.mulVecLin := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change Dᵀ *ᵥ (leftKernelProjector D *ᵥ y) = 0
    rw [Matrix.mulVec_mulVec, transpose_mul_leftKernelProjector D hD, Matrix.zero_mulVec]
  · intro hx
    exact ⟨x, (leftKernelProjector_fixed_iff D hD x).mpr hx⟩

theorem leftKernelProjector_trace (D : Matrix m n ℝ) (hD : Function.Injective D.mulVec) :
    (leftKernelProjector D).trace = Fintype.card m - (Fintype.card n : ℝ) := by
  unfold leftKernelProjector
  rw [Matrix.trace_sub, Matrix.trace_mul_comm (D * (Dᵀ * D)⁻¹) Dᵀ,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_det_isUnit_of_injective D hD)]
  simp

theorem leftKernelProjector_orthogonal_conjugate (D : Matrix m n ℝ) (O : Matrix m m ℝ)
    (hO : Oᵀ * O = 1) : leftKernelProjector (O * D) = O * leftKernelProjector D * Oᵀ := by
  have hOt : O * Oᵀ = 1 := Matrix.mul_eq_one_comm.mp hO
  have hg : (O * D)ᵀ * (O * D) = Dᵀ * D := by
    calc
      _ = Dᵀ * (Oᵀ * O) * D := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hO, Matrix.mul_one]
  unfold leftKernelProjector
  rw [hg]
  simp only [Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, hOt, Matrix.mul_assoc]

theorem IsOrthogonalProjector.entry_norm_le_one {P : Matrix m m ℝ}
    (hP : IsOrthogonalProjector P) (i j : m) : ‖P i j‖ ≤ 1 := by
  have hdiag : P j j ≤ 1 := by
    have h := psd_diagonal_nonneg hP.complement.posSemidef j
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h
    linarith
  have hsum : ∑ k, (P k j) ^ 2 = P j j := by
    have h := congrFun (congrFun hP.idempotent j) j
    have hs : ∀ k, P j k = P k j := fun k => congrFun (congrFun hP.symmetric k) j
    simpa only [Matrix.mul_apply, hs, pow_two] using h
  have hsingle : (P i j) ^ 2 ≤ ∑ k, (P k j) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (P k j)) (Finset.mem_univ i)
  rw [hsum] at hsingle
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg (P i j + 1), sq_nonneg (P i j - 1)]

end
end LowRank
