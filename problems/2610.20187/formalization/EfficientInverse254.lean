import RationalMatrixNewton254
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Hermitian

open Matrix
open scoped BigOperators Matrix
namespace Paper254

def inverseSplit (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n+1) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))

def inverseBlocks {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :=
  A.submatrix (inverseSplit n) (inverseSplit n)

def scalarPivotInverse (a : Matrix (Fin 1) (Fin 1) ℚ) : Matrix (Fin 1) (Fin 1) ℚ :=
  fun _ _=>(a 0 0)⁻¹

def inverseSchur {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  let B := inverseBlocks A
  B.toBlocks₂₂-B.toBlocks₂₁*scalarPivotInverse B.toBlocks₁₁*B.toBlocks₁₂

def inverseAssemble {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (J : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  let B := inverseBlocks A
  let I := scalarPivotInverse B.toBlocks₁₁
  let R := I*B.toBlocks₁₂*J
  let C := J*B.toBlocks₂₁*I
  Matrix.reindex (inverseSplit n) (inverseSplit n)
    (Matrix.fromBlocks (I+R*B.toBlocks₂₁*I) (-R) (-C) J)

/-- Each recursive result is materialized as an array of arrays. -/
def efficientInverseRows : (n : ℕ)→Vector (Vector ℚ n) n→Vector (Vector ℚ n) n
  | 0,A=>A
  | n+1,A=>
    let M := rationalMatrixOfRows A
    let J := rationalMatrixOfRows (efficientInverseRows n (rationalMatrixRows (inverseSchur M)))
    rationalMatrixRows (inverseAssemble M J)

def efficientInverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :=
  rationalMatrixOfRows (efficientInverseRows n (rationalMatrixRows A))

theorem efficientInverse_succ {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    efficientInverse A=inverseAssemble A (efficientInverse (inverseSchur A)) := by
  have hc {d : ℕ} (M : Matrix (Fin d) (Fin d) ℚ) :
      rationalMatrixOfRows (rationalMatrixRows M)=M := by
    ext i j
    simp [rationalMatrixOfRows,rationalMatrixRows,Vector.get]
  simp only [efficientInverse,efficientInverseRows,hc]

theorem scalarPivotInverse_eq (a : Matrix (Fin 1) (Fin 1) ℚ) : scalarPivotInverse a=a⁻¹ := by
  ext i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  simp [scalarPivotInverse]

theorem schur_positive {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (A : Matrix n n ℚ) (B : Matrix n m ℚ) (D : Matrix m m ℚ)
    (hA : A.PosDef) (hM : (fromBlocks A B Bᴴ D).PosDef) :
    (D-Bᴴ*A⁻¹*B).PosDef := by
  letI := hA.isUnit.invertible
  have hD : D.IsHermitian := by
    simpa using hM.1.submatrix Sum.inr
  refine ⟨hD.sub (Matrix.isHermitian_conjTranspose_mul_mul B hA.inv.isHermitian),?_⟩
  intro x hx
  have hn : (-((A⁻¹*B)*ᵥ x) ⊕ᵥ x)≠0 := by
    intro hz
    apply hx
    funext j
    exact congrFun hz (Sum.inr j)
  have hh := hM.2 _ hn
  rw [dotProduct_mulVec,schur_complement_eq₁₁ B D _ _ hA.1,neg_add_cancel,
    dotProduct_zero,zero_add,←dotProduct_mulVec] at hh
  exact hh

theorem positive_submatrix_equiv {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℚ) (hA : A.PosDef) (e : m ≃ n) : (A.submatrix e e).PosDef := by
  refine ⟨hA.1.submatrix e,?_⟩
  intro x hx
  have hy : x ∘ e.symm≠0 := by
    intro hh
    apply hx
    funext j
    simpa using congrFun hh (e j)
  have hh := hA.2 _ hy
  rw [submatrix_mulVec_equiv]
  simpa only [star_trivial,comp_equiv_symm_dotProduct] using hh

theorem positive_first_block {n : ℕ}
    (A : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℚ) (hA : A.PosDef) :
    A.toBlocks₁₁.PosDef := by
  refine ⟨hA.1.submatrix Sum.inl,?_⟩
  intro x hx
  have hn : (x ⊕ᵥ (0:Fin n→ℚ))≠0 := by
    intro hh
    apply hx
    funext j
    exact congrFun hh (Sum.inl j)
  have hh := hA.2 _ hn
  rw [←Matrix.fromBlocks_toBlocks A] at hh
  simpa [Matrix.fromBlocks_mulVec,dotProduct,Matrix.mulVec,Fintype.sum_sum_type] using hh

theorem inverseSchur_pos {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hA : A.PosDef) : (inverseSchur A).PosDef := by
  have hB := positive_submatrix_equiv A hA (inverseSplit n)
  have hfirst := positive_first_block (inverseBlocks A) hB
  have hc : (inverseBlocks A).toBlocks₂₁=(inverseBlocks A).toBlocks₁₂ᴴ := by
    ext i j
    exact (congrArg (fun M=>M (Sum.inr i) (Sum.inl j)) hB.1).symm
  have hh := schur_positive (inverseBlocks A).toBlocks₁₁ (inverseBlocks A).toBlocks₁₂
    (inverseBlocks A).toBlocks₂₂ hfirst (by rw [←hc,fromBlocks_toBlocks]; exact hB)
  simpa only [inverseSchur,scalarPivotInverse_eq,hc] using hh

theorem inverseAssemble_correct {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hA : A.PosDef) : inverseAssemble A (inverseSchur A)⁻¹=A⁻¹ := by
  let B := inverseBlocks A
  have hB : B.PosDef := positive_submatrix_equiv A hA (inverseSplit n)
  have hfirst := positive_first_block B hB
  letI := hfirst.isUnit.invertible
  have hS : (B.toBlocks₂₂-B.toBlocks₂₁*B.toBlocks₁₁⁻¹*B.toBlocks₁₂).PosDef := by
    simpa only [inverseSchur,scalarPivotInverse_eq] using inverseSchur_pos A hA
  letI : Invertible (B.toBlocks₂₂-B.toBlocks₂₁*⅟B.toBlocks₁₁*B.toBlocks₁₂) := by
    rw [Matrix.invOf_eq_nonsing_inv]
    exact hS.isUnit.invertible
  have hF : (fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂).PosDef := by
    rwa [fromBlocks_toBlocks]
  letI := hF.isUnit.invertible
  have hf := Matrix.invOf_fromBlocks₁₁_eq B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂
  simp only [Matrix.invOf_eq_nonsing_inv,fromBlocks_toBlocks] at hf
  calc
    _ = Matrix.reindex (inverseSplit n) (inverseSplit n) B⁻¹ := by
      rw [hf]
      simp only [inverseAssemble,inverseSchur,scalarPivotInverse_eq]
      rfl
    _ = (Matrix.reindex (inverseSplit n) (inverseSplit n) B)⁻¹ :=
      (Matrix.inv_reindex _ _ B).symm
    _ = A⁻¹ := by
      congr 1
      ext i j
      simp [B,inverseBlocks,Matrix.reindex_apply]

/-- Exact correctness for every positive-definite rational input; no pivot
or Schur-invertibility assumptions are supplied by the caller. -/
theorem efficientInverse_correct (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : A.PosDef) : efficientInverse A=A⁻¹ := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    rw [efficientInverse_succ,ih (inverseSchur A) (inverseSchur_pos A hA)]
    exact inverseAssemble_correct A hA

theorem rational_normal_positive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsUnit A) : (Aᵀ*A).PosDef := by
  have hherm : (Aᵀ*A).IsHermitian := by
    simpa using Matrix.isHermitian_transpose_mul_self A
  refine ⟨hherm,?_⟩
  intro x hx
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hA
  have hax : A*ᵥ x≠0 := by
    intro hh
    apply hx
    exact hinj (hh.trans (Matrix.mulVec_zero A).symm)
  have hp : 0<∑ j,(A*ᵥ x) j^2 := by
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hax
    exact Finset.sum_pos' (fun _ _=>sq_nonneg _) ⟨j,Finset.mem_univ _,sq_pos_of_ne_zero hj⟩
  rw [←Matrix.mulVec_mulVec,dotProduct_mulVec,star_trivial,Matrix.vecMul_transpose]
  simpa only [dotProduct,pow_two] using hp

def efficientGeneralInverseRows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Vector (Vector ℚ n) n :=
  let J := rationalMatrixOfRows (efficientInverseRows n (rationalMatrixRows (Aᵀ*A)))
  rationalMatrixRows (J*Aᵀ)

def efficientGeneralInverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :=
  rationalMatrixOfRows (efficientGeneralInverseRows A)

/-- Normal equations extend the exact algorithm to every nonsingular
matrix, including nonsymmetric rounded Newton iterates. -/
theorem efficientGeneralInverse_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsUnit A) : efficientGeneralInverse A=A⁻¹ := by
  have hc {d : ℕ} (M : Matrix (Fin d) (Fin d) ℚ) :
      rationalMatrixOfRows (rationalMatrixRows M)=M := by
    ext i j
    simp [rationalMatrixOfRows,rationalMatrixRows,Vector.get]
  change rationalMatrixOfRows (rationalMatrixRows (efficientInverse (Aᵀ*A)*Aᵀ))=A⁻¹
  rw [hc,efficientInverse_correct _ _ (rational_normal_positive A hA),Matrix.mul_inv_rev,
    Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_transpose A
      (A.isUnit_iff_isUnit_det.mp hA)),Matrix.mul_one]

end Paper254
#print axioms Paper254.efficientInverse_correct
#print axioms Paper254.efficientGeneralInverse_correct
#print axioms Paper254.schur_positive
