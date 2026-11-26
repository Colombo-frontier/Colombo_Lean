import EfficientInverseCost254

open Matrix
open scoped Matrix
namespace Paper254

/-- The recursive call receives the Schur matrix, while its continuation
captures the materialized border, not the previous full input matrix. -/
def countedBorderInverse : (n : ℕ)→Matrix (Fin n) (Fin n) ℚ→Matrix (Fin n) (Fin n) ℚ×ℕ
  | 0,A=>(A,0)
  | n+1,A=>
    let border:=cacheInverseBorder A
    let schur:=countedSchur A
    let child:=countedBorderInverse n schur.1
    let result:=countedBorderAssemble border child.1
    (result.1,schur.2+child.2+result.2)

theorem countedBorderInverse_value (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (countedBorderInverse n A).1=efficientInverse A := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [countedBorderInverse,countedBorderAssemble_value,countedSchur_value,ih,efficientInverse_succ]

theorem countedBorderInverse_cost (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (countedBorderInverse n A).2=inverseArithmeticCount n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countedBorderInverse,countedSchur_cost,countedBorderAssemble_cost,ih,inverseArithmeticCount]
    ring

def countedBorderGeneralInverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ×ℕ :=
  let normal:=countedMatrixMul Aᵀ A
  let inverse:=countedBorderInverse n normal.1
  let result:=countedMatrixMul inverse.1 Aᵀ
  (result.1,normal.2+inverse.2+result.2)

theorem countedBorderGeneralInverse_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsUnit A) : (countedBorderGeneralInverse A).1=A⁻¹ := by
  simp only [countedBorderGeneralInverse,countedMatrixMul_value,countedBorderInverse_value]
  rw [efficientInverse_correct _ _ (rational_normal_positive A hA),Matrix.mul_inv_rev,
    Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_transpose A
      (A.isUnit_iff_isUnit_det.mp hA)),Matrix.mul_one]

theorem countedBorderGeneralInverse_cost {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (countedBorderGeneralInverse A).2≤12*n^3 := by
  simp only [countedBorderGeneralInverse,countedMatrixMul_cost,countedBorderInverse_cost]
  have hh:=inverseArithmeticCount_bound n
  nlinarith

def inverseBorderCells {n : ℕ} (b : InverseBorder n) : ℕ :=
  1+b.row.toList.length+b.column.toList.length

theorem inverseBorderCells_eq {n : ℕ} (b : InverseBorder n) : inverseBorderCells b=2*n+1 := by
  simp [inverseBorderCells]
  omega

/-- Rational-cell workspace in a reference-counted ownership model:
Schur temporaries are released before descent; each continuation holds
only its border; assembly temporaries are released on return. Scalar
instruction counters are ghost data, and input/output cell arrays are
included. The polynomial bit bound charges the size of each such cell. -/
def borderInverseWorkspace : ℕ→ℕ
  | 0=>0
  | n+1=>max ((n+1)^2+(2*n+1)+(1+n+n*n+n*n))
    (max ((2*n+1)+borderInverseWorkspace n) ((2*n+1)+(n*n+6*n+4)))

theorem borderInverseWorkspace_bound (n : ℕ) : borderInverseWorkspace n≤12*n^2 := by
  induction n with
  | zero => simp [borderInverseWorkspace]
  | succ n ih =>
    simp only [borderInverseWorkspace,max_le_iff]
    constructor
    · nlinarith
    · constructor <;> nlinarith

def borderContinuationCells : ℕ→ℕ
  | 0=>0
  | n+1=>2*n+1+borderContinuationCells n

theorem borderContinuationCells_eq (n : ℕ) : borderContinuationCells n=n^2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [borderContinuationCells,ih]; ring

/-- Evaluation annotated with the ownership workspace profile. Its
continuation stores the actual cached border; the cell account lists
the Schur and assembly arrays by their dimensions. -/
def profiledBorderInverse : (n : ℕ)→Matrix (Fin n) (Fin n) ℚ→
    (Matrix (Fin n) (Fin n) ℚ×ℕ)×ℕ
  | 0,A=>((A,0),0)
  | n+1,A=>
    let border:=cacheInverseBorder A
    let schur:=countedSchur A
    let child:=profiledBorderInverse n schur.1
    let result:=countedBorderAssemble border child.1.1
    ((result.1,schur.2+child.1.2+result.2),
      max ((n+1)^2+inverseBorderCells border+(1+n+n*n+n*n))
        (max (inverseBorderCells border+child.2) (inverseBorderCells border+(n*n+6*n+4))))

theorem profiledBorderInverse_program (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (profiledBorderInverse n A).1=countedInverse n A := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [profiledBorderInverse,countedInverse,ih]

theorem profiledBorderInverse_workspace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (profiledBorderInverse n A).2=borderInverseWorkspace n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [profiledBorderInverse,inverseBorderCells_eq,ih,borderInverseWorkspace]

theorem profiledBorderInverse_quadratic_workspace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (profiledBorderInverse n A).2≤12*n^2 := by
  rw [profiledBorderInverse_workspace]
  exact borderInverseWorkspace_bound n

def profiledGeneralInverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (Matrix (Fin n) (Fin n) ℚ×ℕ)×ℕ :=
  let normal:=countedMatrixMul Aᵀ A
  let inverse:=profiledBorderInverse n normal.1
  let result:=countedMatrixMul inverse.1.1 Aᵀ
  ((result.1,normal.2+inverse.1.2+result.2),
    max (3*n^2) (max (n^2+inverse.2) (3*n^2)))

theorem profiledGeneralInverse_program {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (profiledGeneralInverse A).1=countedGeneralInverse A := by
  simp only [profiledGeneralInverse,profiledBorderInverse_program,countedGeneralInverse]

theorem profiledGeneralInverse_quadratic_workspace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (profiledGeneralInverse A).2≤13*n^2 := by
  have hh:=profiledBorderInverse_quadratic_workspace n (countedMatrixMul Aᵀ A).1
  simp only [profiledGeneralInverse,max_le_iff]
  constructor
  · omega
  · constructor <;> omega

end Paper254
#print axioms Paper254.countedBorderGeneralInverse_correct
#print axioms Paper254.countedBorderGeneralInverse_cost
#print axioms Paper254.borderInverseWorkspace_bound
#print axioms Paper254.profiledGeneralInverse_program
#print axioms Paper254.profiledGeneralInverse_quadratic_workspace

