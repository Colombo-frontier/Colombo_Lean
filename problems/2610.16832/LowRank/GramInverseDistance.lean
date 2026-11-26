import LowRank.KernelProjectorMeasurable

/-! The first diagonal entry of an inverse Gram matrix is the reciprocal
squared distance of the first column from the remaining column space. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def prependColumn {d s : ℕ} (x : Fin d → ℝ) (Y : Matrix (Fin d) (Fin s) ℝ) :
    Matrix (Fin d) (Fin (s + 1)) ℝ := fun i => Fin.cons (x i) (Y i)

theorem prependColumn_mulVec {d s : ℕ} (x : Fin d → ℝ) (Y : Matrix (Fin d) (Fin s) ℝ)
    (z : Fin (s + 1) → ℝ) :
    prependColumn x Y *ᵥ z = z 0 • x + Y *ᵥ (fun j => z j.succ) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, prependColumn,
    Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem prependColumn_transpose_mulVec {d s : ℕ} (x : Fin d → ℝ)
    (Y : Matrix (Fin d) (Fin s) ℝ) (z : Fin d → ℝ) :
    (prependColumn x Y)ᵀ *ᵥ z = Fin.cons (x ⬝ᵥ z) (Yᵀ *ᵥ z) := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem tail_injective_of_prependColumn {d s : ℕ} (x : Fin d → ℝ)
    (Y : Matrix (Fin d) (Fin s) ℝ) (hX : Function.Injective (prependColumn x Y).mulVec) :
    Function.Injective Y.mulVec := by
  intro u v huv
  have h : prependColumn x Y *ᵥ Fin.cons 0 u = prependColumn x Y *ᵥ Fin.cons 0 v := by
    simp only [prependColumn_mulVec, Fin.cons_zero, Fin.cons_succ, zero_smul, zero_add, huv]
  have heq := hX h
  funext j
  exact congrFun heq j.succ

theorem leftKernelProjector_mul_self {d s : ℕ} (Y : Matrix (Fin d) (Fin s) ℝ)
    (hY : Function.Injective Y.mulVec) : leftKernelProjector Y * Y = 0 := by
  have h := congrArg Matrix.transpose (transpose_mul_leftKernelProjector Y hY)
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero,
    (leftKernelProjector_isProjector Y).symmetric] using h

theorem gram_inverse_first_distance_mul {d s : ℕ} (x : Fin d → ℝ)
    (Y : Matrix (Fin d) (Fin s) ℝ) (hX : Function.Injective (prependColumn x Y).mulVec) :
    (((prependColumn x Y)ᵀ * prependColumn x Y)⁻¹ 0 0) *
      (x ⬝ᵥ (leftKernelProjector Y *ᵥ x)) = 1 := by
  let X := prependColumn x Y
  let u := (Xᵀ * X)⁻¹ *ᵥ (Pi.single 0 1 : Fin (s + 1) → ℝ)
  have hY := tail_injective_of_prependColumn x Y hX
  have hu0 : u 0 = (Xᵀ * X)⁻¹ 0 0 := by simp [u, Matrix.mulVec, dotProduct, Pi.single_apply]
  have heq : Xᵀ *ᵥ (X *ᵥ u) = Pi.single 0 1 := by
    rw [Matrix.mulVec_mulVec]
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (gram_det_isUnit_of_injective X hX), Matrix.one_mulVec]
  have hx : x ⬝ᵥ (X *ᵥ u) = 1 := by
    have h := congrFun heq 0
    change x ⬝ᵥ (X *ᵥ u) = (Pi.single 0 1 : Fin (s + 1) → ℝ) 0 at h
    simpa using h
  have hy : Yᵀ *ᵥ (X *ᵥ u) = 0 := by
    ext j
    have h := congrFun heq j.succ
    change (Yᵀ *ᵥ (X *ᵥ u)) j = (Pi.single 0 1 : Fin (s + 1) → ℝ) j.succ at h
    simpa [Pi.single_apply] using h
  have hfix := (leftKernelProjector_fixed_iff Y hY (X *ᵥ u)).mpr hy
  have hres : X *ᵥ u = u 0 • (leftKernelProjector Y *ᵥ x) := by
    calc
      X *ᵥ u = leftKernelProjector Y *ᵥ (X *ᵥ u) := hfix.symm
      _ = _ := by
        rw [show X = prependColumn x Y from rfl, prependColumn_mulVec,
          Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
          leftKernelProjector_mul_self Y hY, Matrix.zero_mulVec, add_zero]
  rw [hres, dotProduct_smul, smul_eq_mul, hu0] at hx
  exact hx

theorem gram_inverse_first_distance {d s : ℕ} (x : Fin d → ℝ)
    (Y : Matrix (Fin d) (Fin s) ℝ) (hX : Function.Injective (prependColumn x Y).mulVec) :
    ((prependColumn x Y)ᵀ * prependColumn x Y)⁻¹ 0 0 =
      (x ⬝ᵥ (leftKernelProjector Y *ᵥ x))⁻¹ := by
  have h := gram_inverse_first_distance_mul x Y hX
  have hn : x ⬝ᵥ (leftKernelProjector Y *ᵥ x) ≠ 0 := by intro hz; rw [hz, mul_zero] at h; norm_num at h
  apply (mul_right_cancel₀ hn)
  rw [inv_mul_cancel₀ hn]
  exact h

theorem projector_quadratic_eq_image_sq {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (x : Fin d → ℝ) :
    x ⬝ᵥ (P *ᵥ x) = (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
  calc
    (x ⬝ᵥ (P *ᵥ x)) = x ⬝ᵥ (P *ᵥ (P *ᵥ x)) := by rw [Matrix.mulVec_mulVec, hP.idempotent]
    _ = _ := by rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hP.symmetric]

theorem gram_inverse_first_distance_sq {d s : ℕ} (x : Fin d → ℝ)
    (Y : Matrix (Fin d) (Fin s) ℝ) (hX : Function.Injective (prependColumn x Y).mulVec) :
    ((prependColumn x Y)ᵀ * prependColumn x Y)⁻¹ 0 0 =
      ((leftKernelProjector Y *ᵥ x) ⬝ᵥ (leftKernelProjector Y *ᵥ x))⁻¹ := by
  rw [gram_inverse_first_distance x Y hX, projector_quadratic_eq_image_sq (leftKernelProjector_isProjector Y)]

end
end LowRank
