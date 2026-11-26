import LowRank.FactorKernelProjector

/-! Exact containment of the represented matrix imposes linear constraints
on its residual block. If the residual coefficient vanishes, invertibility
of the exposed block and completeness of the row basis force the entire
left annihilator to vanish. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem mul_lower_block_left {d q r s : ℕ}
    (M : Matrix (Fin d) (Fin q ⊕ Fin r) ℝ)
    (A : Matrix (Fin q) (Fin q) ℝ) (C : Matrix (Fin r) (Fin q) ℝ)
    (D : Matrix (Fin r) (Fin s) ℝ) :
    (M * fromBlocks A 0 C D).submatrix id Sum.inl =
      M.submatrix id Sum.inl * A + M.submatrix id Sum.inr * C := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix, Fintype.sum_sum_type]

theorem mul_lower_block_right {d q r s : ℕ}
    (M : Matrix (Fin d) (Fin q ⊕ Fin r) ℝ)
    (A : Matrix (Fin q) (Fin q) ℝ) (C : Matrix (Fin r) (Fin q) ℝ)
    (D : Matrix (Fin r) (Fin s) ℝ) :
    (M * fromBlocks A 0 C D).submatrix id Sum.inr = M.submatrix id Sum.inr * D := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix, Fintype.sum_sum_type]

theorem representedMatrix_annihilator_core {d t q r s : ℕ}
    (st : FactorData d t q r s) (hst : st.Orthogonal)
    (Q : Matrix (Fin d) (Fin d) ℝ) (D : Matrix (Fin r) (Fin s) ℝ)
    (h : Q * representedMatrix st D = 0) :
    (Q * st.2.1) * fromBlocks st.1.1 0 st.1.2 D = 0 := by
  have heq := congrArg (fun X => X * st.2.2) h
  simpa only [representedMatrix, Matrix.mul_assoc, hst.2.2.1, Matrix.mul_one,
    Matrix.zero_mul] using heq

theorem representedMatrix_annihilator_residual {d t q r s : ℕ}
    (st : FactorData d t q r s) (hst : st.Orthogonal)
    (Q : Matrix (Fin d) (Fin d) ℝ) (D : Matrix (Fin r) (Fin s) ℝ)
    (h : Q * representedMatrix st D = 0) :
    (Q * st.2.1).submatrix id Sum.inr * D = 0 := by
  have heq := congrArg (fun X : Matrix (Fin d) (Fin q ⊕ Fin s) ℝ =>
    X.submatrix id Sum.inr) (representedMatrix_annihilator_core st hst Q D h)
  simpa only [mul_lower_block_right, Matrix.submatrix_zero] using heq

theorem representedMatrix_annihilator_zero_of_residual_coefficient_zero {d t q r s : ℕ}
    (st : FactorData d t q r s) (hst : st.Orthogonal) (hA : IsUnit st.1.1)
    (Q : Matrix (Fin d) (Fin d) ℝ) (D : Matrix (Fin r) (Fin s) ℝ)
    (h : Q * representedMatrix st D = 0)
    (hright : (Q * st.2.1).submatrix id Sum.inr = 0) : Q = 0 := by
  have hleft := congrArg (fun X : Matrix (Fin d) (Fin q ⊕ Fin s) ℝ =>
    X.submatrix id Sum.inl) (representedMatrix_annihilator_core st hst Q D h)
  dsimp only at hleft
  rw [mul_lower_block_left] at hleft
  change (Q * st.2.1).submatrix id Sum.inl * st.1.1 +
    (Q * st.2.1).submatrix id Sum.inr * st.1.2 = 0 at hleft
  rw [hright, Matrix.zero_mul, add_zero] at hleft
  have hdet : IsUnit st.1.1.det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hleftzero := congrArg (fun X => X * st.1.1⁻¹) hleft
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
    Matrix.zero_mul] at hleftzero
  have hQB : Q * st.2.1 = 0 := by
    ext i j
    cases j with
    | inl j => exact congrFun (congrFun hleftzero i) j
    | inr j => exact congrFun (congrFun hright i) j
  calc
    Q = Q * (st.2.1 * st.2.1ᵀ) := by rw [hst.2.1, Matrix.mul_one]
    _ = 0 := by rw [← Matrix.mul_assoc, hQB, Matrix.zero_mul]

end
end LowRank
