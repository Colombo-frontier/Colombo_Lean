import GaussianState254

noncomputable section
open scoped Matrix BigOperators
open Matrix
namespace Paper254

theorem precision_bilinear_symm {d : ℕ} {A : Precision d} (hA : A.IsHermitian)
    (x y : Coordinates d) : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  have ht : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  calc
    _ = (x ᵥ* A) ⬝ᵥ y := Matrix.dotProduct_mulVec _ _ _
    _ = (A *ᵥ x) ⬝ᵥ y := by rw [← Matrix.mulVec_transpose, ht]
    _ = _ := dotProduct_comm _ _

theorem precision_inverse_cancel {d : ℕ} {A : Precision d} (hA : A.PosDef)
    (x : Coordinates d) : A *ᵥ (A⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)),
    Matrix.one_mulVec]

theorem precision_inverse_cancel_left {d : ℕ} {A : Precision d} (hA : A.PosDef)
    (x : Coordinates d) : A⁻¹ *ᵥ (A *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)),
    Matrix.one_mulVec]

theorem matrixQuadratic_add_smul {d : ℕ} {A : Precision d} (hA : A.IsHermitian)
    (x y : Coordinates d) (k : ℝ) :
    matrixQuadratic A (x+k • y) =
      matrixQuadratic A x+2*k*(x ⬝ᵥ (A *ᵥ y))+k^2*matrixQuadratic A y := by
  simp only [matrixQuadratic, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [precision_bilinear_symm hA y x]
  ring

theorem rankOnePrecision_det {d : ℕ} {A : Precision d} (hA : A.PosDef)
    (θ : ℝ) (g : Coordinates d) :
    (rankOnePrecision A θ g).det = A.det*(1+θ*matrixQuadratic A⁻¹ g) := by
  have he : θ • Matrix.vecMulVec g g = Matrix.vecMulVec (θ • g) g := by
    ext i j
    simp [Matrix.vecMulVec, mul_assoc]
  have hd := Matrix.det_add_replicateCol_mul_replicateRow (ι := Unit)
    (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)) (θ • g) g
  have hr : (1+Matrix.replicateRow Unit g*A⁻¹*Matrix.replicateCol Unit (θ • g)).det =
      1+θ*matrixQuadratic A⁻¹ g := by
    rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec]
    simp only [Matrix.det_unique, Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.replicateRow_mul_replicateCol_apply, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul, matrixQuadratic]
  rw [hr] at hd
  change (A+θ • Matrix.vecMulVec g g).det = _
  rw [he, Matrix.vecMulVec_eq Unit]
  exact hd

theorem rankOnePrecision_inverse_gradient {d : ℕ} {A : Precision d} (hA : A.PosDef)
    (θ : ℝ) (hθ : 0 ≤ θ) (g : Coordinates d) :
    (rankOnePrecision A θ g)⁻¹ *ᵥ g =
      (1/(1+θ*matrixQuadratic A⁻¹ g)) • (A⁻¹ *ᵥ g) := by
  let v := matrixQuadratic A⁻¹ g
  have hv : 0 ≤ v := matrixQuadratic_nonneg hA.inv g
  have hden : 0 < 1+θ*v := by nlinarith [mul_nonneg hθ hv]
  have hsolve : rankOnePrecision A θ g *ᵥ ((1/(1+θ*v)) • (A⁻¹ *ᵥ g)) = g := by
    simp only [rankOnePrecision, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
      precision_inverse_cancel hA, Matrix.vecMulVec_mulVec]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
    change (1/(1+θ*v))*(g j+θ*(g j*v)) = g j
    field_simp [ne_of_gt hden]
  have hnew := rankOnePrecision_posDef hA θ hθ g
  have hh := congrArg (fun x => (rankOnePrecision A θ g)⁻¹ *ᵥ x) hsolve
  dsimp only at hh
  rw [precision_inverse_cancel_left hnew] at hh
  exact hh.symm

end Paper254
#print axioms Paper254.rankOnePrecision_det
#print axioms Paper254.rankOnePrecision_inverse_gradient
