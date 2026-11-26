import GaussianHistory254
import ComputationalCost254

noncomputable section
open scoped BigOperators Matrix
open Matrix
namespace Paper254

def countedRealDot : List (ℝ×ℝ)→ℝ×ℕ
  | [] => (0,0)
  | (a,b)::xs => let tail := countedRealDot xs; (a*b+tail.1,tail.2+2)

theorem countedRealDot_spec (xs : List (ℝ×ℝ)) :
    countedRealDot xs=((xs.map (fun p=>p.1*p.2)).sum,2*xs.length) := by
  induction xs with
  | nil => rfl
  | cons p xs ih => rcases p with ⟨a,b⟩; simp [countedRealDot,ih,Nat.mul_add,Nat.add_comm]

def countedRealVector {d : ℕ} (f : Fin d→ℝ×ℕ) : Coordinates d×ℕ :=
  let rows := Vector.ofFn f
  (fun i=>(rows.get i).1,(rows.toList.map Prod.snd).sum)

theorem countedRealVector_value {d : ℕ} (f : Fin d→ℝ×ℕ) :
    (countedRealVector f).1=fun i=>(f i).1 := by ext i; simp [countedRealVector,Vector.get]

theorem countedRealVector_cost {d c : ℕ} (f : Fin d→ℝ×ℕ) (hc : ∀ i,(f i).2=c) :
    (countedRealVector f).2=d*c := by
  simp [countedRealVector,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,hc]

def countedRealMatrix {m n : ℕ} (f : Fin m→Fin n→ℝ×ℕ) :
    Matrix (Fin m) (Fin n) ℝ×ℕ :=
  let rows := Vector.ofFn (fun i=>Vector.ofFn (f i))
  (fun i j=>((rows.get i).get j).1,
    (rows.toList.map (fun row=>(row.toList.map Prod.snd).sum)).sum)

theorem countedRealMatrix_value {m n : ℕ} (f : Fin m→Fin n→ℝ×ℕ) :
    (countedRealMatrix f).1=fun i j=>(f i j).1 := by
  ext i j; simp [countedRealMatrix,Vector.get]

theorem countedRealMatrix_cost {m n c : ℕ} (f : Fin m→Fin n→ℝ×ℕ)
    (hc : ∀ i j,(f i j).2=c) : (countedRealMatrix f).2=m*n*c := by
  simp [countedRealMatrix,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,hc,Nat.mul_assoc]

def countedRealMatVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n→ℝ) :=
  countedRealVector (fun i=>countedRealDot (List.ofFn (fun j=>(A i j,x j))))

theorem countedRealMatVec_value {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n→ℝ) :
    (countedRealMatVec A x).1=A*ᵥx := by
  ext i
  simp [countedRealMatVec,countedRealVector_value,countedRealDot_spec,
    List.map_ofFn,List.sum_ofFn,Matrix.mulVec,dotProduct]

theorem countedRealMatVec_cost {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n→ℝ) :
    (countedRealMatVec A x).2=2*m*n := by
  unfold countedRealMatVec
  rw [countedRealVector_cost _ (c:=2*n) (by intro i; simp [countedRealDot_spec])]
  ring

def countedRealMul {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin k) ℝ) :=
  countedRealMatrix (fun i j=>countedRealDot (List.ofFn (fun l=>(A i l,B l j))))

theorem countedRealMul_value {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin k) ℝ) : (countedRealMul A B).1=A*B := by
  ext i j
  simp [countedRealMul,countedRealMatrix_value,countedRealDot_spec,
    List.map_ofFn,List.sum_ofFn,Matrix.mul_apply]

theorem countedRealMul_cost {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin k) ℝ) : (countedRealMul A B).2=2*m*n*k := by
  unfold countedRealMul
  rw [countedRealMatrix_cost _ (c:=2*n) (by intro i j; simp [countedRealDot_spec])]
  ring

theorem spectral_solve {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c b : Coordinates d) (hc : ∀ j,0<c j) :
    (U : Precision d)ᴴ*ᵥ(fun j=>((U : Precision d)*ᵥb) j/c j)=
      (rotatedPrecision U c)⁻¹*ᵥb := by
  apply unitary_mulVec_injective U
  have hsolve : rotatedPrecision U c *ᵥ
      ((U : Precision d)ᴴ*ᵥ(fun j=>((U : Precision d)*ᵥb) j/c j))=b := by
    simp only [rotatedPrecision,← Matrix.mulVec_mulVec]
    have hu (x : Coordinates d) : (U : Precision d)*ᵥ((U : Precision d)ᴴ*ᵥx)=x := by
      rw [Matrix.mulVec_mulVec,←star_eq_conjTranspose,←unitary.coe_star,
        unitary.coe_mul_star_self,Matrix.one_mulVec]
    rw [hu]
    have hdiag : Matrix.diagonal c *ᵥ(fun j=>((U : Precision d)*ᵥb) j/c j)=
        (U : Precision d)*ᵥb := by
      ext j
      simp [Matrix.mulVec_diagonal,mul_div_cancel₀ _ (hc j).ne']
    rw [hdiag,Matrix.mulVec_mulVec,←star_eq_conjTranspose,
      unitary.coe_star_mul_self,Matrix.one_mulVec]
  have he := congrArg (fun x=>(rotatedPrecision U c)⁻¹*ᵥx) hsolve
  dsimp only at he
  rw [precision_inverse_cancel_left (rotatedPrecision_posDef U c hc)] at he
  exact congrArg (fun x=>(U : Precision d)*ᵥx) he

end Paper254
#print axioms Paper254.spectral_solve
