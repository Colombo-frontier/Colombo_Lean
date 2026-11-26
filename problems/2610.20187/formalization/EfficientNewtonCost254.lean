import EfficientInverseCost254
import EfficientNewton254

open Matrix
open scoped BigOperators Matrix
namespace Paper254

/-- A materialized unary operation. `charge` is the specified scalar
primitive cost; rounding costs remain an explicit interface. -/
def countedMatrixUnary {m n : ℕ} (op : ℚ→ℚ) (charge : ℕ)
    (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℚ×ℕ :=
  let rows : Vector (Vector (ℚ×ℕ) n) m :=
    Vector.ofFn (fun i=>Vector.ofFn (fun j=>(op (A i j),charge)))
  (fun i j=>((rows.get i).get j).1,
    (rows.toList.map (fun row=>(row.toList.map Prod.snd).sum)).sum)

theorem countedMatrixUnary_value {m n : ℕ} (op : ℚ→ℚ) (charge : ℕ)
    (A : Matrix (Fin m) (Fin n) ℚ) :
    (countedMatrixUnary op charge A).1=fun i j=>op (A i j) := by
  ext i j
  simp [countedMatrixUnary,Vector.get]

theorem countedMatrixUnary_cost {m n : ℕ} (op : ℚ→ℚ) (charge : ℕ)
    (A : Matrix (Fin m) (Fin n) ℚ) : (countedMatrixUnary op charge A).2=charge*m*n := by
  simp [countedMatrixUnary,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]
  ring

def countedNewtonStep {d : ℕ} (p roundCost : ℕ)
    (A X : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin d) (Fin d) ℚ×ℕ :=
  let I := countedGeneralInverse X
  let M := countedMatrixMul I.1 A
  let S := countedMatrixZip (·+·) X M.1
  let R := countedMatrixUnary (fun x=>dyadicCeil p ((1/2:ℚ)*x)) (1+roundCost) S.1
  (R.1,I.2+M.2+S.2+R.2)

theorem countedNewtonStep_value {d : ℕ} (p roundCost : ℕ)
    (A X : Matrix (Fin d) (Fin d) ℚ) (hX : IsUnit X) :
    (countedNewtonStep p roundCost A X).1=rationalMatrixNewtonStep p A X := by
  simp only [countedNewtonStep,countedMatrixUnary_value,countedMatrixZip_add,
    countedMatrixMul_value,countedGeneralInverse_correct X hX]
  rw [rationalMatrixNewtonStep,rationalMatrixInverse_eq_inv]
  rfl

theorem countedNewtonStep_cost {d : ℕ} (hd : 0<d) (p roundCost : ℕ)
    (A X : Matrix (Fin d) (Fin d) ℚ) :
    (countedNewtonStep p roundCost A X).2≤(16+roundCost)*d^3 := by
  have hi := countedGeneralInverse_cost X
  simp only [countedNewtonStep,countedMatrixUnary_cost,countedMatrixZip_cost,countedMatrixMul_cost]
  have hd2 : d*d≤d*d*d := by nlinarith
  have hc := Nat.mul_le_mul_left roundCost hd2
  nlinarith

def countedNewton {d : ℕ} (p roundCost : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) :
    ℕ→Matrix (Fin d) (Fin d) ℚ×ℕ
  | 0=>(X,0)
  | n+1=>
    let prev := countedNewton p roundCost A X n
    let next := countedNewtonStep p roundCost A prev.1
    (next.1,prev.2+next.2)

theorem countedNewton_value {d : ℕ} (p roundCost : ℕ)
    (A X : Matrix (Fin d) (Fin d) ℚ) (N : ℕ)
    (hunit : ∀ k<N,IsUnit (realMatrix (rationalMatrixNewton p A X k))) :
    (countedNewton p roundCost A X N).1=rationalMatrixNewton p A X N := by
  induction N with
  | zero => rw [rationalMatrixNewton_zero]; rfl
  | succ n ih =>
    have he := ih (fun k hk=>hunit k (by omega))
    simp only [countedNewton,he,countedNewtonStep_value p roundCost _ _
      (realMatrix_unit_reflect _ (hunit n (by omega))),rationalMatrixNewton_succ]

theorem countedNewton_cost {d : ℕ} (hd : 0<d) (p roundCost : ℕ)
    (A X : Matrix (Fin d) (Fin d) ℚ) (N : ℕ) :
    (countedNewton p roundCost A X N).2≤N*(16+roundCost)*d^3 := by
  induction N with
  | zero => simp [countedNewton]
  | succ n ih =>
    have hh := countedNewtonStep_cost hd p roundCost A (countedNewton p roundCost A X n).1
    simp only [countedNewton]
    nlinarith

end Paper254
#print axioms Paper254.countedNewton_value
#print axioms Paper254.countedNewton_cost
