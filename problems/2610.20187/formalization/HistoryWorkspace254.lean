import EfficientBorderInverse254
import EfficientHistoryCost254

open Matrix
namespace Paper254

/-- Workspace annotations use owned rational cells. Matrix results are
materialized by the counted kernels; completed temporaries are released.
Projection-oracle workspace is supplied separately. -/
def profiledNewtonStep {d : ℕ} (p roundCost : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) :=
  let I:=profiledGeneralInverse X
  let M:=countedMatrixMul I.1.1 A
  let S:=countedMatrixZip (·+·) X M.1
  let R:=countedMatrixUnary (fun x=>dyadicCeil p ((1/2:ℚ)*x)) (1+roundCost) S.1
  ((R.1,I.1.2+M.2+S.2+R.2),max (2*d^2+I.2) (6*d^2))

theorem profiledNewtonStep_program {d : ℕ} (p roundCost : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) :
    (profiledNewtonStep p roundCost A X).1=countedNewtonStep p roundCost A X := by
  simp only [profiledNewtonStep,profiledGeneralInverse_program,countedNewtonStep]

theorem profiledNewtonStep_workspace {d : ℕ} (p roundCost : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) :
    (profiledNewtonStep p roundCost A X).2≤20*d^2 := by
  have hi:=profiledGeneralInverse_quadratic_workspace X
  simp only [profiledNewtonStep,max_le_iff]
  constructor <;> omega

def profiledNewton {d : ℕ} (p roundCost : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) :
    ℕ→(Matrix (Fin d) (Fin d) ℚ×ℕ)×ℕ
  | 0=>((X,0),2*d^2)
  | n+1=>
    let prev:=profiledNewton p roundCost A X n
    let next:=profiledNewtonStep p roundCost A prev.1.1
    ((next.1.1,prev.1.2+next.1.2),max prev.2 next.2)

theorem profiledNewton_program {d : ℕ} (p roundCost : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) (N : ℕ) :
    (profiledNewton p roundCost A X N).1=countedNewton p roundCost A X N := by
  induction N with
  | zero => rfl
  | succ n ih => simp only [profiledNewton,ih,profiledNewtonStep_program,countedNewton]

theorem profiledNewton_workspace {d : ℕ} (p roundCost : ℕ) (A X : Matrix (Fin d) (Fin d) ℚ) (N : ℕ) :
    (profiledNewton p roundCost A X N).2≤20*d^2 := by
  induction N with
  | zero => simp [profiledNewton]; omega
  | succ n ih =>
    simp only [profiledNewton,max_le_iff]
    exact ⟨ih,profiledNewtonStep_workspace _ _ _ _⟩

def profiledPositivePart {d : ℕ} (a L s roundCost : ℕ) (eps : ℚ) (M : Matrix (Fin d) (Fin d) ℚ) :=
  let input:=countedSqrtInput eps M
  let power:=countedRatPow 2 L
  let start:=countedMatrixScale power.1 (1:Matrix (Fin d) (Fin d) ℚ)
  let root:=profiledNewton (matrixSqrtPrecision a L s) roundCost input.1 start.1 (matrixSqrtIterations a L s)
  let symmetricSum:=countedMatrixZip (·+·) root.1.1 root.1.1ᵀ
  let symmetric:=countedMatrixScale (1/2) symmetricSum.1
  let sum:=countedMatrixZip (·+·) M symmetric.1
  let out:=countedMatrixScale (1/2) sum.1
  ((out.1,input.2+power.2+start.2+root.1.2+symmetricSum.2+symmetric.2+sum.2+out.2),
    max (10*(d+1)^2) (3*d^2+root.2))

theorem profiledPositivePart_program {d : ℕ} (a L s roundCost : ℕ) (eps : ℚ) (M : Matrix (Fin d) (Fin d) ℚ) :
    (profiledPositivePart a L s roundCost eps M).1=countedPositivePart a L s roundCost eps M := by
  simp only [profiledPositivePart,profiledNewton_program,countedPositivePart]

theorem profiledPositivePart_workspace {d : ℕ} (a L s roundCost : ℕ) (eps : ℚ) (M : Matrix (Fin d) (Fin d) ℚ) :
    (profiledPositivePart a L s roundCost eps M).2≤30*(d+1)^2 := by
  have hd2 : d^2≤(d+1)^2 := Nat.pow_le_pow_left (Nat.le_succ d) 2
  have hh:=profiledNewton_workspace (matrixSqrtPrecision a L s) roundCost
    (countedSqrtInput eps M).1 (countedMatrixScale (countedRatPow 2 L).1 1).1 (matrixSqrtIterations a L s)
  simp only [profiledPositivePart,max_le_iff]
  constructor <;> omega

def profiledSpectralClip {d : ℕ} (a L s roundCost : ℕ) (eps lo hi : ℚ) (M : Matrix (Fin d) (Fin d) ℚ) :=
  let lower:=countedMatrixScale lo (1:Matrix (Fin d) (Fin d) ℚ)
  let upper:=countedMatrixScale hi (1:Matrix (Fin d) (Fin d) ℚ)
  let leftInput:=countedMatrixZip (·-·) M lower.1
  let rightInput:=countedMatrixZip (·-·) M upper.1
  let left:=profiledPositivePart a L s roundCost eps leftInput.1
  let right:=profiledPositivePart a L s roundCost eps rightInput.1
  let sum:=countedMatrixZip (·+·) lower.1 left.1.1
  let out:=countedMatrixZip (·-·) sum.1 right.1.1
  ((out.1,lower.2+upper.2+leftInput.2+rightInput.2+left.1.2+right.1.2+sum.2+out.2),
    max (8*(d+1)^2) (max (5*d^2+left.2) (6*d^2+right.2)))

theorem profiledSpectralClip_program {d : ℕ} (a L s roundCost : ℕ) (eps lo hi : ℚ) (M : Matrix (Fin d) (Fin d) ℚ) :
    (profiledSpectralClip a L s roundCost eps lo hi M).1=countedSpectralClip a L s roundCost eps lo hi M := by
  simp only [profiledSpectralClip,profiledPositivePart_program,countedSpectralClip]

theorem profiledSpectralClip_workspace {d : ℕ} (a L s roundCost : ℕ) (eps lo hi : ℚ) (M : Matrix (Fin d) (Fin d) ℚ) :
    (profiledSpectralClip a L s roundCost eps lo hi M).2≤40*(d+1)^2 := by
  have hd2 : d^2≤(d+1)^2 := Nat.pow_le_pow_left (Nat.le_succ d) 2
  have hl:=profiledPositivePart_workspace a L s roundCost eps
    (countedMatrixZip (·-·) M (countedMatrixScale lo 1).1).1
  have hu:=profiledPositivePart_workspace a L s roundCost eps
    (countedMatrixZip (·-·) M (countedMatrixScale hi 1).1).1
  simp only [profiledSpectralClip,max_le_iff]
  constructor
  · omega
  · constructor <;> omega

def profiledTiltMatrices {d : ℕ} (S : RationalHistoryData d) (lam : ℚ) (g : Fin d→ℚ) :=
  let P:=profiledGeneralInverse S.covariance
  let scalar : ℚ×ℕ := (2*(lam*lam),2)
  let rank:=countedMatrixMul (rationalColumn g) (rationalColumn g)ᵀ
  let scaled:=countedMatrixScale scalar.1 rank.1
  let Q:=countedMatrixZip (·+·) P.1.1 scaled.1
  let V:=profiledGeneralInverse Q.1
  (((P.1.1,V.1.1),P.1.2+scalar.2+rank.2+scaled.2+Q.2+V.1.2),
    max (8*(d+1)^2) (max (3*d^2+P.2) (5*d^2+V.2)))

theorem profiledTiltMatrices_program {d : ℕ} (S : RationalHistoryData d) (lam : ℚ) (g : Fin d→ℚ) :
    (profiledTiltMatrices S lam g).1=countedTiltMatrices S lam g := by
  simp only [profiledTiltMatrices,profiledGeneralInverse_program,countedTiltMatrices]

theorem profiledTiltMatrices_workspace {d : ℕ} (S : RationalHistoryData d) (lam : ℚ) (g : Fin d→ℚ) :
    (profiledTiltMatrices S lam g).2≤25*(d+1)^2 := by
  have hd2 : d^2≤(d+1)^2 := Nat.pow_le_pow_left (Nat.le_succ d) 2
  have hp:=profiledGeneralInverse_quadratic_workspace S.covariance
  have hv:=profiledGeneralInverse_quadratic_workspace
    (countedMatrixZip (·+·) (profiledGeneralInverse S.covariance).1.1
      (countedMatrixScale (2*(lam*lam)) (countedMatrixMul (rationalColumn g) (rationalColumn g)ᵀ).1).1).1
  simp only [profiledTiltMatrices,max_le_iff]
  constructor
  · omega
  · constructor <;> omega

def profiledHistoryStep {d : ℕ} (roundCost projectionCost projectionWorkspace : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) :=
  let tilt:=profiledTiltMatrices S lam g
  let clip:=profiledSpectralClip cfg.dimensionLog cfg.spectralLog cfg.accuracy roundCost
    cfg.smoothing cfg.lowerThreshold cfg.upperThreshold tilt.1.1.2
  let C:=countedMatrixUnary (dyadicCeil cfg.storagePrecision) roundCost clip.1.1
  let invC:=profiledGeneralInverse C.1
  let B:=countedMatrixUnary (dyadicCeil cfg.storagePrecision) roundCost invC.1.1
  let mean:=countedTiltMeanFrom roundCost cfg.storagePrecision tilt.1.1.1 tilt.1.1.2 S.mean lam g w
  let projected:=Vector.ofFn (oracle B.1 mean.1 cfg.projectionPrecision)
  (((⟨fun j=>projected.get j,C.1⟩:RationalHistoryData d),
    tilt.1.2+clip.1.2+C.2+invC.1.2+B.2+mean.2+projectionCost),
    max (18*(d+1)^2) (max (4*d^2+tilt.2)
      (max (6*d^2+clip.2) (max (7*d^2+invC.2) (8*d^2+projectionWorkspace)))))

theorem profiledHistoryStep_program {d : ℕ} (roundCost projectionCost projectionWorkspace : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) :
    (profiledHistoryStep roundCost projectionCost projectionWorkspace oracle cfg S lam g w).1=
      countedHistoryStep roundCost projectionCost oracle cfg S lam g w := by
  simp only [profiledHistoryStep,profiledTiltMatrices_program,profiledSpectralClip_program,
    profiledGeneralInverse_program,countedHistoryStep]

theorem profiledHistoryStep_workspace {d : ℕ} (roundCost projectionCost projectionWorkspace : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) :
    (profiledHistoryStep roundCost projectionCost projectionWorkspace oracle cfg S lam g w).2≤
      60*(d+1)^2+projectionWorkspace := by
  have hd2 : d^2≤(d+1)^2 := Nat.pow_le_pow_left (Nat.le_succ d) 2
  have ht:=profiledTiltMatrices_workspace S lam g
  have hc:=profiledSpectralClip_workspace cfg.dimensionLog cfg.spectralLog cfg.accuracy roundCost
    cfg.smoothing cfg.lowerThreshold cfg.upperThreshold (profiledTiltMatrices S lam g).1.1.2
  have hi:=profiledGeneralInverse_quadratic_workspace
    (countedMatrixUnary (dyadicCeil cfg.storagePrecision) roundCost
      (profiledSpectralClip cfg.dimensionLog cfg.spectralLog cfg.accuracy roundCost
        cfg.smoothing cfg.lowerThreshold cfg.upperThreshold (profiledTiltMatrices S lam g).1.1.2).1.1).1
  simp only [profiledHistoryStep,max_le_iff]
  constructor
  · omega
  · constructor
    · omega
    · constructor
      · omega
      · constructor <;> omega

end Paper254
#print axioms Paper254.profiledHistoryStep_program
#print axioms Paper254.profiledHistoryStep_workspace



