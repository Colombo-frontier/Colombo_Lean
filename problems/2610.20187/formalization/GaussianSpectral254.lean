import GaussianAlgebra254

noncomputable section
open scoped Matrix BigOperators
open Matrix
namespace Paper254

def rotatedPrecision {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) : Precision d :=
  (U : Precision d)ᴴ * Matrix.diagonal c * (U : Precision d)

theorem unitary_mulVec_injective {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ) :
    Function.Injective (fun x : Coordinates d => (U : Precision d) *ᵥ x) := by
  intro x y h
  have hh := congrArg (fun z => (star U : Matrix.unitaryGroup (Fin d) ℝ).val *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, unitary.coe_star, unitary.coe_star_mul_self,
    Matrix.one_mulVec] using hh

theorem rotatedPrecision_posDef {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hc : ∀ j, 0 < c j) : (rotatedPrecision U c).PosDef := by
  exact (Matrix.posDef_diagonal_iff.mpr hc).conjTranspose_mul_mul_same
    (unitary_mulVec_injective U)

theorem rotatedPrecision_quadratic {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c x : Coordinates d) :
    matrixQuadratic (rotatedPrecision U c) x =
      ∑ j, c j*((U : Precision d) *ᵥ x) j^2 := by
  unfold matrixQuadratic rotatedPrecision
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.dotProduct_mulVec x (U : Precision d)ᵀ, Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rotatedPrecision_trace {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) : (rotatedPrecision U c).trace = ∑ j, c j := by
  unfold rotatedPrecision
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [← star_eq_conjTranspose, ← unitary.coe_star, unitary.coe_mul_star_self, Matrix.one_mul,
    Matrix.trace_diagonal]

theorem rotatedPrecision_det {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) : (rotatedPrecision U c).det = ∏ j, c j := by
  have hdet : (U : Precision d)ᴴ.det*(U : Precision d).det = 1 := by
    rw [← Matrix.det_mul, ← star_eq_conjTranspose, unitary.coe_star_mul_self,
      Matrix.det_one]
  simp only [rotatedPrecision, Matrix.det_mul, Matrix.det_diagonal]
  calc
    _ = ((U : Precision d)ᴴ.det*(U : Precision d).det)*(∏ j, c j) := by ring
    _ = _ := by rw [hdet, one_mul]

theorem rotatedPrecision_potential {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c x : Coordinates d) (q : ℝ) (hq : 0 < q) (hc : ∀ j, 0 < c j) :
    (precisionCovariancePart q (rotatedPrecision U c)+
      matrixQuadratic (rotatedPrecision U c) x)/2 =
      ∑ j, (q*c j-1-Real.log (q*c j)+c j*((U : Precision d) *ᵥ x) j^2)/2 := by
  have hp : q^d*(∏ j, c j) = ∏ j, q*c j := by
    rw [Finset.prod_mul_distrib]
    simp
  rw [precisionCovariancePart, rotatedPrecision_trace, rotatedPrecision_det, hp,
    Real.log_prod Finset.univ _ (fun j _ => ne_of_gt (mul_pos hq (hc j))),
    rotatedPrecision_quadratic]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end Paper254
#print axioms Paper254.rotatedPrecision_potential
