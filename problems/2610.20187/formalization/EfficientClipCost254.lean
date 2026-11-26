import EfficientNewtonCost254
import EfficientSpectralClip254

open Matrix
open scoped BigOperators Matrix
namespace Paper254

def countedMatrixScale {m n : ℕ} (c : ℚ) (A : Matrix (Fin m) (Fin n) ℚ) :=
  countedMatrixUnary (fun x=>c*x) 1 A

theorem countedMatrixScale_value {m n : ℕ} (c : ℚ) (A : Matrix (Fin m) (Fin n) ℚ) :
    (countedMatrixScale c A).1=c • A := countedMatrixUnary_value _ _ A

theorem countedMatrixScale_cost {m n : ℕ} (c : ℚ) (A : Matrix (Fin m) (Fin n) ℚ) :
    (countedMatrixScale c A).2=m*n := by simp [countedMatrixScale,countedMatrixUnary_cost]

def countedRatPow (a : ℚ) : ℕ→ℚ×ℕ
  | 0=>(1,0)
  | n+1=>let v:=countedRatPow a n; (v.1*a,v.2+1)

theorem countedRatPow_spec (a : ℚ) (n : ℕ) : countedRatPow a n=(a^n,n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countedRatPow,ih,pow_succ]

def countedSqrtInput {d : ℕ} (eps : ℚ) (A : Matrix (Fin d) (Fin d) ℚ) :=
  let prod:=countedMatrixMul A A
  let square : ℚ×ℕ := (eps*eps,1)
  let shift:=countedMatrixScale square.1 (1:Matrix (Fin d) (Fin d) ℚ)
  let out:=countedMatrixZip (·+·) prod.1 shift.1
  (out.1,prod.2+square.2+shift.2+out.2)

theorem countedSqrtInput_value {d : ℕ} (eps : ℚ) (A : Matrix (Fin d) (Fin d) ℚ) :
    (countedSqrtInput eps A).1=rationalSqrtInput eps A := by
  simp only [countedSqrtInput,countedMatrixMul_value,countedMatrixScale_value,countedMatrixZip_add]
  simp only [rationalSqrtInput,pow_two]

theorem countedSqrtInput_cost {d : ℕ} (eps : ℚ) (A : Matrix (Fin d) (Fin d) ℚ) :
    (countedSqrtInput eps A).2=2*d^3+2*d^2+1 := by
  simp only [countedSqrtInput,countedMatrixMul_cost,countedMatrixScale_cost,countedMatrixZip_cost]
  ring

def countedPositivePart {d : ℕ} (a L s roundCost : ℕ) (eps : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin d) (Fin d) ℚ×ℕ :=
  let input:=countedSqrtInput eps M
  let power:=countedRatPow 2 L
  let start:=countedMatrixScale power.1 (1:Matrix (Fin d) (Fin d) ℚ)
  let root:=countedNewton (matrixSqrtPrecision a L s) roundCost input.1 start.1
    (matrixSqrtIterations a L s)
  let symmetricSum:=countedMatrixZip (·+·) root.1 root.1ᵀ
  let symmetric:=countedMatrixScale (1/2) symmetricSum.1
  let sum:=countedMatrixZip (·+·) M symmetric.1
  let out:=countedMatrixScale (1/2) sum.1
  (out.1,input.2+power.2+start.2+root.2+symmetricSum.2+symmetric.2+sum.2+out.2)

theorem countedPositivePart_value {d : ℕ} (a L s roundCost : ℕ) (eps : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ)
    (hunit : ∀ k<matrixSqrtIterations a L s,IsUnit (realMatrix (rationalMatrixNewton
      (matrixSqrtPrecision a L s) (rationalSqrtInput eps M) ((2:ℚ)^L • 1) k))) :
    (countedPositivePart a L s roundCost eps M).1=rationalPositivePart a L s eps M := by
  simp only [countedPositivePart,countedMatrixScale_value,countedMatrixZip_add,
    countedRatPow_spec,countedSqrtInput_value,countedNewton_value _ roundCost _ _ _ hunit]
  rfl

theorem countedPositivePart_cost {d : ℕ} (hd : 0<d) (a L s roundCost : ℕ) (eps : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) :
    (countedPositivePart a L s roundCost eps M).2≤
      (matrixSqrtIterations a L s*(16+roundCost)+10)*d^3+L := by
  have hn := countedNewton_cost hd (matrixSqrtPrecision a L s) roundCost
    (countedSqrtInput eps M).1 (countedMatrixScale (countedRatPow 2 L).1
      (1:Matrix (Fin d) (Fin d) ℚ)).1 (matrixSqrtIterations a L s)
  simp only [countedPositivePart,countedMatrixScale_cost,countedMatrixZip_cost,
    countedRatPow_spec,countedSqrtInput_cost]
  simp only [countedRatPow_spec] at hn
  have hd2 : d*d≤d*d*d := by nlinarith
  have hd3 : 1≤d*d*d := by nlinarith
  nlinarith

def countedSpectralClip {d : ℕ} (a L s roundCost : ℕ) (eps lo hi : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin d) (Fin d) ℚ×ℕ :=
  let lower:=countedMatrixScale lo (1:Matrix (Fin d) (Fin d) ℚ)
  let upper:=countedMatrixScale hi (1:Matrix (Fin d) (Fin d) ℚ)
  let leftInput:=countedMatrixZip (·-·) M lower.1
  let rightInput:=countedMatrixZip (·-·) M upper.1
  let left:=countedPositivePart a L s roundCost eps leftInput.1
  let right:=countedPositivePart a L s roundCost eps rightInput.1
  let sum:=countedMatrixZip (·+·) lower.1 left.1
  let out:=countedMatrixZip (·-·) sum.1 right.1
  (out.1,lower.2+upper.2+leftInput.2+rightInput.2+left.2+right.2+sum.2+out.2)

theorem countedSpectralClip_value {d : ℕ} (a L s roundCost : ℕ) (eps lo hi : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ)
    (hunit : ∀ z∈({lo,hi}:Finset ℚ),∀ k<matrixSqrtIterations a L s,
      IsUnit (realMatrix (rationalMatrixNewton (matrixSqrtPrecision a L s)
        (rationalSqrtInput eps (M-z • 1)) ((2:ℚ)^L • 1) k))) :
    (countedSpectralClip a L s roundCost eps lo hi M).1=rationalSpectralClip a L s eps lo hi M := by
  simp only [countedSpectralClip,countedMatrixScale_value,countedMatrixZip_sub,countedMatrixZip_add]
  rw [countedPositivePart_value _ _ _ _ _ _ (hunit lo (by simp)),
    countedPositivePart_value _ _ _ _ _ _ (hunit hi (by simp))]
  rfl

theorem countedSpectralClip_cost {d : ℕ} (hd : 0<d) (a L s roundCost : ℕ) (eps lo hi : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) :
    (countedSpectralClip a L s roundCost eps lo hi M).2≤
      (2*matrixSqrtIterations a L s*(16+roundCost)+26)*d^3+2*L := by
  have hl := countedPositivePart_cost hd a L s roundCost eps
    (countedMatrixZip (·-·) M (countedMatrixScale lo 1).1).1
  have hu := countedPositivePart_cost hd a L s roundCost eps
    (countedMatrixZip (·-·) M (countedMatrixScale hi 1).1).1
  simp only [countedSpectralClip,countedMatrixScale_cost,countedMatrixZip_cost]
  have hd2 : d*d≤d*d*d := by nlinarith
  nlinarith

theorem spectralClipNewton_units {d : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (eps lo hi : ℚ) (heps : 0<(eps:ℝ))
    (M : Matrix (Fin d) (Fin d) ℚ) (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hM : realMatrix M=rotatedPrecision U c)
    (hsmall : ((2:ℝ)^L)⁻¹≤(eps:ℝ))
    (hl : ∀ j,|c j-(lo:ℝ)|+(eps:ℝ)≤(2:ℝ)^L)
    (hu : ∀ j,|c j-(hi:ℝ)|+(eps:ℝ)≤(2:ℝ)^L) :
    ∀ z∈({lo,hi}:Finset ℚ),∀ k<matrixSqrtIterations a L s,
      IsUnit (realMatrix (rationalMatrixNewton (matrixSqrtPrecision a L s)
        (rationalSqrtInput eps (M-z • 1)) ((2:ℚ)^L • 1) k)) := by
  intro z hz k hk
  have hb : ∀ j,|c j-(z:ℝ)|+(eps:ℝ)≤(2:ℝ)^L := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl
    · exact hl
    · exact hu
  let v : Coordinates d := fun j=>(c j-(z:ℝ))^2+(eps:ℝ)^2
  have hv : ∀ j,0<v j := by intro j; dsimp [v]; nlinarith [sq_nonneg (c j-(z:ℝ))]
  have hslo : ∀ j,((2:ℝ)^L)⁻¹≤Real.sqrt (v j) := by
    intro j
    have hh := Real.sq_sqrt (hv j).le
    have he : (eps:ℝ)≤Real.sqrt (v j) := by
      dsimp [v] at hh
      nlinarith [sq_nonneg (c j-(z:ℝ)),Real.sqrt_nonneg (v j)]
    exact hsmall.trans he
  have hshi : ∀ j,Real.sqrt (v j)≤(2:ℝ)^L := by
    intro j
    have hh := Real.sq_sqrt (hv j).le
    have he : Real.sqrt (v j)≤|c j-(z:ℝ)|+(eps:ℝ) := by
      dsimp [v] at hh
      nlinarith [sq_abs (c j-(z:ℝ)),abs_nonneg (c j-(z:ℝ)),
        mul_nonneg (abs_nonneg (c j-(z:ℝ))) heps.le,Real.sqrt_nonneg (v j)]
    exact he.trans (hb j)
  exact certifiedMatrixSqrt_units hd a L s hdim (rationalSqrtInput eps (M-z • 1)) U v hv
    (rationalSqrtInput_spectral eps (M-z • 1) U (fun j=>c j-(z:ℝ))
      (realMatrix_shift_spectral M U c hM z)) hslo hshi k hk.le

end Paper254
#print axioms Paper254.countedSpectralClip_value
#print axioms Paper254.countedSpectralClip_cost
#print axioms Paper254.spectralClipNewton_units
