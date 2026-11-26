import MatrixRounding254
import InverseStability254
import Mathlib.Analysis.Matrix

open scoped Matrix.Norms.Operator BigOperators NNReal
open Matrix
namespace Paper254

/-- A rational inverse evaluated with rational arithmetic. -/
def rationalMatrixInverse {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) :=
  A.det⁻¹ • A.adjugate

def rationalMatrixNewtonStep {d : ℕ} (p : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) :=
  roundRationalMatrix p ((1/2:ℚ) • (X+rationalMatrixInverse X*A))

def cacheRationalMatrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin d) (Fin d) ℚ :=
  let rows := Vector.ofFn (fun i=>Vector.ofFn (fun j=>A i j))
  fun i j=>(rows.get i).get j

theorem cacheRationalMatrix_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) :
    cacheRationalMatrix A=A := by
  ext i j
  simp [cacheRationalMatrix,Vector.get]

def rationalMatrixRows {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) : Vector (Vector ℚ d) d :=
  Vector.ofFn (fun i=>Vector.ofFn (fun j=>A i j))

def rationalMatrixOfRows {d : ℕ} (rows : Vector (Vector ℚ d) d) : Matrix (Fin d) (Fin d) ℚ :=
  fun i j=>(rows.get i).get j

def rationalMatrixNewtonRows {d : ℕ} (p : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) :
    ℕ → Vector (Vector ℚ d) d
  | 0 => rationalMatrixRows X
  | n+1 => rationalMatrixRows (rationalMatrixNewtonStep p A
      (rationalMatrixOfRows (rationalMatrixNewtonRows p A X n)))

def rationalMatrixNewton {d : ℕ} (p : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) (n : ℕ) :=
  rationalMatrixOfRows (rationalMatrixNewtonRows p A X n)

theorem rationalMatrixNewton_zero {d : ℕ} (p : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) :
    rationalMatrixNewton p A X 0=X := by
  ext i j
  simp [rationalMatrixNewton,rationalMatrixNewtonRows,rationalMatrixRows,rationalMatrixOfRows,Vector.get]

theorem rationalMatrixNewton_succ {d : ℕ} (p n : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) :
    rationalMatrixNewton p A X (n+1)=rationalMatrixNewtonStep p A (rationalMatrixNewton p A X n) := by
  ext i j
  simp [rationalMatrixNewton,rationalMatrixNewtonRows,rationalMatrixRows,rationalMatrixOfRows,Vector.get]

noncomputable def realMatrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) : Precision d :=
  (Rat.castHom ℝ).mapMatrix A

theorem realMatrix_inverse {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) :
    realMatrix (rationalMatrixInverse A)=Ring.inverse (realMatrix A) := by
  rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_def, Ring.inverse_eq_inv]
  have ha := (Rat.castHom ℝ).map_adjugate A
  ext i j
  change ((A.det⁻¹*A.adjugate i j:ℚ):ℝ) = _
  push_cast
  have he := congrArg (fun B : Precision d => B i j) ha
  change (A.adjugate i j:ℝ)=(realMatrix A).adjugate i j at he
  rw [he]
  rfl

theorem matrix_operator_norm_of_entries {d : ℕ} (A : Precision d) (e : ℝ)
    (he : 0 ≤ e) (hA : ∀ i j, |A i j| ≤ e) : ‖A‖ ≤ d*e := by
  rw [Matrix.linfty_opNorm_def]
  change ((Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ : ℝ≥0):ℝ) ≤ _
  rw [← NNReal.coe_natCast, ← NNReal.coe_mk e he, ← NNReal.coe_mul, NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i _
  calc
    _ ≤ ∑ _j : Fin d, (⟨e,he⟩:ℝ≥0) := by
      apply Finset.sum_le_sum
      intro j _
      exact hA i j
    _ = _ := by simp

theorem rationalMatrixNewtonStep_error {d : ℕ} (p : ℕ)
    (A X : Matrix (Fin d) (Fin d) ℚ) :
    ‖realMatrix (rationalMatrixNewtonStep p A X)-
      algebraNewtonStep (realMatrix A) (realMatrix X)‖ ≤ d*((2:ℝ)^p)⁻¹ := by
  have hcast : realMatrix ((1/2:ℚ) • (X+rationalMatrixInverse X*A)) =
      algebraNewtonStep (realMatrix A) (realMatrix X) := by
    rw [algebraNewtonStep, ← realMatrix_inverse X]
    ext i j
    change (((1/2:ℚ)*(X i j+∑ k,rationalMatrixInverse X i k*A k j):ℚ):ℝ) =
      (1/2:ℝ)*((X i j:ℝ)+∑ k,(rationalMatrixInverse X i k:ℝ)*(A k j:ℝ))
    push_cast
    rfl
  rw [← hcast]
  apply matrix_operator_norm_of_entries _ _ (by positivity)
  intro i j
  exact roundRationalMatrix_entry p _ i j

/-- Fixed-denominator storage is restored after each matrix update. -/
theorem rationalMatrixNewton_encoding {d : ℕ} (p n : ℕ)
    (A X : Matrix (Fin d) (Fin d) ℚ) (i j : Fin d) :
    ∃ z : ℤ, rationalMatrixNewton p A X (n+1) i j=(z:ℚ)/(2:ℚ)^p := by
  rw [rationalMatrixNewton_succ]
  exact ⟨_,rfl⟩

end Paper254
#print axioms Paper254.realMatrix_inverse
#print axioms Paper254.rationalMatrixNewtonStep_error
