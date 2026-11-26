import MatrixArithmeticCost254
import EfficientInverse254

open Matrix
open scoped BigOperators Matrix
namespace Paper254

/-- Materialized entrywise arithmetic; one scalar operation per entry. -/
def countedMatrixZip {m n : ℕ} (op : ℚ→ℚ→ℚ)
    (A B : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℚ×ℕ :=
  let rows : Vector (Vector (ℚ×ℕ) n) m :=
    Vector.ofFn (fun i=>Vector.ofFn (fun j=>(op (A i j) (B i j),1)))
  (fun i j=>((rows.get i).get j).1,
    (rows.toList.map (fun row=>(row.toList.map Prod.snd).sum)).sum)

theorem countedMatrixZip_value {m n : ℕ} (op : ℚ→ℚ→ℚ)
    (A B : Matrix (Fin m) (Fin n) ℚ) :
    (countedMatrixZip op A B).1=fun i j=>op (A i j) (B i j) := by
  ext i j
  simp [countedMatrixZip,Vector.get]

theorem countedMatrixZip_cost {m n : ℕ} (op : ℚ→ℚ→ℚ)
    (A B : Matrix (Fin m) (Fin n) ℚ) : (countedMatrixZip op A B).2=m*n := by
  simp [countedMatrixZip,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]

theorem countedMatrixZip_sub {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    (countedMatrixZip (·-·) A B).1=A-B := countedMatrixZip_value _ A B

theorem countedMatrixZip_add {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    (countedMatrixZip (·+·) A B).1=A+B := countedMatrixZip_value _ A B

def countedSchur {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    Matrix (Fin n) (Fin n) ℚ×ℕ :=
  let B := inverseBlocks A
  let pivot : ℚ×ℕ := ((B.toBlocks₁₁ 0 0)⁻¹,1)
  let I : Matrix (Fin 1) (Fin 1) ℚ := fun _ _=>pivot.1
  let U := countedMatrixMul B.toBlocks₂₁ I
  let V := countedMatrixMul U.1 B.toBlocks₁₂
  let S := countedMatrixZip (·-·) B.toBlocks₂₂ V.1
  (S.1,pivot.2+U.2+V.2+S.2)

theorem countedSchur_value {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    (countedSchur A).1=inverseSchur A := by
  simp only [countedSchur,countedMatrixZip_sub,countedMatrixMul_value]
  rfl

theorem countedSchur_cost {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    (countedSchur A).2=3*n^2+2*n+1 := by
  simp [countedSchur,countedMatrixZip_cost,countedMatrixMul_cost]
  ring

def countedAssemble {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (J : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ×ℕ :=
  let B := inverseBlocks A
  let pivot : ℚ×ℕ := ((B.toBlocks₁₁ 0 0)⁻¹,1)
  let I : Matrix (Fin 1) (Fin 1) ℚ := fun _ _=>pivot.1
  let R₀ := countedMatrixMul I B.toBlocks₁₂
  let R := countedMatrixMul R₀.1 J
  let C₀ := countedMatrixMul J B.toBlocks₂₁
  let C := countedMatrixMul C₀.1 I
  let U := countedMatrixMul R.1 B.toBlocks₂₁
  let V := countedMatrixMul U.1 I
  let W := countedMatrixZip (·+·) I V.1
  let negR := countedMatrixZip (·-·) 0 R.1
  let negC := countedMatrixZip (·-·) 0 C.1
  (Matrix.reindex (inverseSplit n) (inverseSplit n)
      (Matrix.fromBlocks W.1 negR.1 negC.1 J),
    pivot.2+R₀.2+R.2+C₀.2+C.2+U.2+V.2+W.2+negR.2+negC.2)

theorem countedAssemble_value {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (J : Matrix (Fin n) (Fin n) ℚ) : (countedAssemble A J).1=inverseAssemble A J := by
  simp only [countedAssemble,countedMatrixZip_sub,countedMatrixZip_add,countedMatrixMul_value,zero_sub]
  rfl

theorem countedAssemble_cost {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (J : Matrix (Fin n) (Fin n) ℚ) : (countedAssemble A J).2=4*n^2+8*n+4 := by
  simp [countedAssemble,countedMatrixZip_cost,countedMatrixMul_cost]
  ring

/-- Only these border entries survive a recursive call. In particular the
old lower-right block is absent from the continuation frame. -/
structure InverseBorder (n : ℕ) where
  pivot : ℚ
  row : Vector ℚ n
  column : Vector ℚ n

def cacheInverseBorder {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) : InverseBorder n :=
  let B:=inverseBlocks A
  ⟨B.toBlocks₁₁ 0 0,Vector.ofFn (fun j=>B.toBlocks₁₂ 0 j),Vector.ofFn (fun i=>B.toBlocks₂₁ i 0)⟩

def inverseBorderMatrix {n : ℕ} (b : InverseBorder n) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Matrix.reindex (inverseSplit n) (inverseSplit n) (Matrix.fromBlocks
    (fun _ _=>b.pivot) (fun _ j=>b.row.get j) (fun i _=>b.column.get i) 0)

theorem inverseBlocks_border {n : ℕ} (b : InverseBorder n) :
    inverseBlocks (inverseBorderMatrix b)=Matrix.fromBlocks
      (fun _ _=>b.pivot) (fun _ j=>b.row.get j) (fun i _=>b.column.get i) 0 := by
  ext i j
  simp [inverseBlocks,inverseBorderMatrix,Matrix.submatrix_apply,Matrix.reindex_apply]

theorem cacheInverseBorder_pivot {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    (fun (_ _:Fin 1)=>(cacheInverseBorder A).pivot)=(inverseBlocks A).toBlocks₁₁ := by
  ext i j
  have hi : i=0:=Subsingleton.elim _ _
  have hj : j=0:=Subsingleton.elim _ _
  subst i; subst j
  rfl

theorem cacheInverseBorder_row {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    (fun (_:Fin 1) (j:Fin n)=>(cacheInverseBorder A).row.get j)=(inverseBlocks A).toBlocks₁₂ := by
  ext i j
  have hi : i=0:=Subsingleton.elim _ _
  subst i
  simp [cacheInverseBorder,Vector.get]

theorem cacheInverseBorder_column {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    (fun (i:Fin n) (_:Fin 1)=>(cacheInverseBorder A).column.get i)=(inverseBlocks A).toBlocks₂₁ := by
  ext i j
  have hj : j=0:=Subsingleton.elim _ _
  subst j
  simp [cacheInverseBorder,Vector.get]

def countedBorderAssemble {n : ℕ} (b : InverseBorder n) (J : Matrix (Fin n) (Fin n) ℚ) :=
  countedAssemble (inverseBorderMatrix b) J

theorem countedBorderAssemble_value {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (J : Matrix (Fin n) (Fin n) ℚ) :
    (countedBorderAssemble (cacheInverseBorder A) J).1=inverseAssemble A J := by
  simp only [countedBorderAssemble,countedAssemble_value,inverseAssemble,inverseBlocks_border,
    cacheInverseBorder_pivot,cacheInverseBorder_row,cacheInverseBorder_column]
  rfl

theorem countedBorderAssemble_cost {n : ℕ} (b : InverseBorder n) (J : Matrix (Fin n) (Fin n) ℚ) :
    (countedBorderAssemble b J).2=4*n^2+8*n+4 := countedAssemble_cost _ J

/-- The instrumented recursive program executes the same Schur elimination
as the cached inverse. Its output includes the arithmetic instruction count. -/
def countedInverse : (n : ℕ)→Matrix (Fin n) (Fin n) ℚ→Matrix (Fin n) (Fin n) ℚ×ℕ
  | 0,A=>(A,0)
  | n+1,A=>
    let border := cacheInverseBorder A
    let S := countedSchur A
    let J := countedInverse n S.1
    let B := countedBorderAssemble border J.1
    (B.1,S.2+J.2+B.2)

theorem countedInverse_value (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (countedInverse n A).1=efficientInverse A := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [countedInverse,countedSchur_value,countedBorderAssemble_value,ih,efficientInverse_succ]

def inverseArithmeticCount : ℕ→ℕ
  | 0=>0
  | n+1=>inverseArithmeticCount n+7*n^2+10*n+5

theorem countedInverse_cost (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (countedInverse n A).2=inverseArithmeticCount n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countedInverse,countedSchur_cost,countedBorderAssemble_cost,ih,inverseArithmeticCount]
    ring

theorem inverseArithmeticCount_bound (n : ℕ) : inverseArithmeticCount n≤8*n^3 := by
  induction n with
  | zero => simp [inverseArithmeticCount]
  | succ n ih =>
    simp only [inverseArithmeticCount]
    nlinarith [sq_nonneg (n:ℤ)]

def countedGeneralInverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ×ℕ :=
  let N := countedMatrixMul Aᵀ A
  let J := countedInverse n N.1
  let B := countedMatrixMul J.1 Aᵀ
  (B.1,N.2+J.2+B.2)

theorem countedGeneralInverse_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : IsUnit A) : (countedGeneralInverse A).1=A⁻¹ := by
  simp only [countedGeneralInverse,countedMatrixMul_value,countedInverse_value]
  rw [efficientInverse_correct _ _ (rational_normal_positive A hA),Matrix.mul_inv_rev,
    Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_transpose A
      (A.isUnit_iff_isUnit_det.mp hA)),Matrix.mul_one]

theorem countedGeneralInverse_cost {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (countedGeneralInverse A).2≤12*n^3 := by
  simp only [countedGeneralInverse,countedMatrixMul_cost,countedInverse_cost]
  have hh := inverseArithmeticCount_bound n
  nlinarith

end Paper254
#print axioms Paper254.countedGeneralInverse_correct
#print axioms Paper254.countedGeneralInverse_cost
#eval (Paper254.countedGeneralInverse !![(2:ℚ),0;0,3]).2

