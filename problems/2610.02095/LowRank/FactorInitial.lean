import LowRank.FactorProcessRank

/-! Initialize the adaptive factorization at an arbitrary actual input
matrix, with no previously exposed coordinates. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def initialBasis (d : ℕ) : Matrix (Fin d) (Fin 0 ⊕ Fin d) ℝ :=
  (1 : Matrix (Fin d) (Fin d) ℝ).submatrix id (Equiv.emptySum (Fin 0) (Fin d))

def initialFactorData (d t : ℕ) : FactorData d t 0 d t :=
  ((0, 0), (initialBasis d, initialBasis t))

theorem initialBasis_transpose_mul (d : ℕ) : (initialBasis d)ᵀ * initialBasis d = 1 := by
  ext i j
  cases i with
  | inl i => exact Fin.elim0 i
  | inr i =>
    cases j with
    | inl j => exact Fin.elim0 j
    | inr j => simp [initialBasis, Matrix.mul_apply, Matrix.one_apply, Equiv.emptySum]

theorem initialBasis_mul_transpose (d : ℕ) : initialBasis d * (initialBasis d)ᵀ = 1 := by
  ext i j
  simp [initialBasis, Matrix.mul_apply, Matrix.one_apply, Equiv.emptySum,
    Fintype.sum_sum_type]

theorem initialFactorData_orthogonal (d t : ℕ) : (initialFactorData d t).Orthogonal :=
  ⟨initialBasis_transpose_mul d, initialBasis_mul_transpose d,
    initialBasis_transpose_mul t, initialBasis_mul_transpose t⟩

theorem initialFactorData_A_injective (d t : ℕ) :
    Function.Injective (Matrix.mulVec (initialFactorData d t).1.1) :=
  fun _ _ _ => Subsingleton.elim _ _

theorem initialFactorData_represents (d t : ℕ) (X : Matrix (Fin d) (Fin t) ℝ) :
    representedMatrix (initialFactorData d t) X = X := by
  ext i j
  simp [representedMatrix, initialFactorData, initialBasis, Matrix.mul_apply,
    Matrix.one_apply, Equiv.emptySum, Fintype.sum_sum_type]

theorem initialFactorData_final_reconstruct (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : GaussianPolicy r s n S) (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :
    let out := runGaussianPolicy r s n policy p
    representedMatrix
      (finalFactorData (r + n) (s + n) r s n 0 policy
        (fun _ => initialFactorData (r + n) (s + n)) out.1) out.2 = p.2 := by
  dsimp only
  rw [finalFactorData_preserves_matrix, initialFactorData_represents]

/-- Complete matrix invariants for a genuine iid input, under every measurable
policy on the enlarged history. Oracle-program normalization is separate. -/
theorem gaussianPolicy_factorization_ae (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] (policy : GaussianPolicy r s n S)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      let out := runGaussianPolicy r s n policy p
      let st := finalFactorData (r + n) (s + n) r s n 0 policy
        (fun _ => initialFactorData (r + n) (s + n)) out.1
      representedMatrix st out.2 = p.2 ∧ st.Orthogonal ∧
        IsUnit st.1.1 := by
  have hA := runGaussianPolicy_factor_A_injective_ae (r + n) (s + n) r s n 0 ν policy
    (fun _ => initialFactorData (r + n) (s + n)) hv
    (Filter.Eventually.of_forall (fun _ => initialFactorData_A_injective _ _))
  filter_upwards [hA] with p hp
  exact ⟨initialFactorData_final_reconstruct r s n policy p,
    finalFactorData_orthogonal _ _ r s n 0 policy _
      (fun _ => initialFactorData_orthogonal _ _) _, Matrix.mulVec_injective_iff_isUnit.mp hp⟩

end
end LowRank
