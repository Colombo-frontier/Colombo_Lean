import ComputationalCost254
import RationalMatrixNewton254

open scoped BigOperators
open Matrix
namespace Paper254

/-- One rational multiplication and one addition per pair. The counter is
for arithmetic instructions; bit lengths are not charged as unit time. -/
def countedDot : List (ℚ×ℚ)→ℚ×ℕ
  | [] => (0,0)
  | (a,b)::xs => let rest := countedDot xs
                 (a*b+rest.1,rest.2+2)

theorem countedDot_spec (xs : List (ℚ×ℚ)) :
    countedDot xs=((xs.map (fun p=>p.1*p.2)).sum,2*xs.length) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨a,b⟩
    simp [countedDot,ih,Nat.mul_add,Nat.add_comm]

def countedMatrixRows {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin k) ℚ) : Vector (Vector (ℚ×ℕ) k) m :=
  Vector.ofFn (fun i=>Vector.ofFn (fun j=>countedDot (List.ofFn (fun l=>(A i l,B l j)))))

/-- The nested vectors materialize each computed entry and its arithmetic
counter. Reading the result and counting work never recomputes a dot product. -/
def countedMatrixMul {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin k) ℚ) : Matrix (Fin m) (Fin k) ℚ×ℕ :=
  let rows := countedMatrixRows A B
  (fun i j=>((rows.get i).get j).1,
    (rows.toList.map (fun row=>(row.toList.map Prod.snd).sum)).sum)

theorem countedMatrixRows_get {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin k) ℚ) (i : Fin m) (j : Fin k) :
    ((countedMatrixRows A B).get i).get j=((A*B) i j,2*n) := by
  simp [countedMatrixRows,Vector.get,countedDot_spec,List.map_ofFn,List.sum_ofFn,Matrix.mul_apply]

theorem countedMatrixMul_value {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin k) ℚ) : (countedMatrixMul A B).1=A*B := by
  ext i j
  exact congrArg Prod.fst (countedMatrixRows_get A B i j)

theorem countedMatrixMul_cost {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin k) ℚ) : (countedMatrixMul A B).2=2*m*n*k := by
  simp [countedMatrixMul,countedMatrixRows,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,
    countedDot_spec]
  ring

end Paper254
#print axioms Paper254.countedMatrixMul_value
#print axioms Paper254.countedMatrixMul_cost
#eval Paper254.countedMatrixMul (m:=2) (n:=2) (k:=2) !![1,2;3,4] !![5,6;7,8] |>.2
