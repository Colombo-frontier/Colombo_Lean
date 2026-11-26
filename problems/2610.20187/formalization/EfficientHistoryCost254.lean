import EfficientClipCost254
import EfficientHistory254

open Matrix
open scoped BigOperators Matrix
namespace Paper254

def rationalColumn {d : ℕ} (x : Fin d→ℚ) : Matrix (Fin d) (Fin 1) ℚ := fun i _=>x i

theorem rationalColumn_mul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) (x : Fin d→ℚ) :
    A*rationalColumn x=rationalColumn (A*ᵥ x) := by
  ext i j
  rfl

def countedTiltMatrices {d : ℕ} (S : RationalHistoryData d) (lam : ℚ) (g : Fin d→ℚ) :=
  let P:=countedGeneralInverse S.covariance
  let scalar : ℚ×ℕ := (2*(lam*lam),2)
  let rank:=countedMatrixMul (rationalColumn g) (rationalColumn g)ᵀ
  let scaled:=countedMatrixScale scalar.1 rank.1
  let Q:=countedMatrixZip (·+·) P.1 scaled.1
  let V:=countedGeneralInverse Q.1
  ((P.1,V.1),P.2+scalar.2+rank.2+scaled.2+Q.2+V.2)

theorem rationalColumn_outer {d : ℕ} (g : Fin d→ℚ) :
    rationalColumn g*(rationalColumn g)ᵀ=Matrix.vecMulVec g g := by
  ext i j
  simp [Matrix.mul_apply,rationalColumn,Matrix.vecMulVec]

theorem countedTiltMatrices_value {d : ℕ} (S : RationalHistoryData d)
    (hS : (realMatrix S.covariance).PosDef) (lam : ℚ) (g : Fin d→ℚ) :
    (countedTiltMatrices S lam g).1=(rationalMatrixInverse S.covariance,
      rationalMatrixInverse (rationalTiltPrecision S lam g)) := by
  have hp := countedGeneralInverse_correct S.covariance (realMatrix_unit_reflect _ hS.isUnit)
  have hq := countedGeneralInverse_correct (rationalTiltPrecision S lam g)
    (realMatrix_unit_reflect _ (rationalTiltPrecision_posDef S hS lam g).isUnit)
  rw [←rationalMatrixInverse_eq_inv] at hp hq
  simp only [countedTiltMatrices,hp,countedMatrixMul_value,rationalColumn_outer,
    countedMatrixScale_value,countedMatrixZip_add,←pow_two]
  exact congrArg (fun V=>(rationalMatrixInverse S.covariance,V)) hq

theorem countedTiltMatrices_cost {d : ℕ} (S : RationalHistoryData d) (lam : ℚ) (g : Fin d→ℚ) :
    (countedTiltMatrices S lam g).2≤24*d^3+4*d^2+2 := by
  have hp:=countedGeneralInverse_cost S.covariance
  have hv:=countedGeneralInverse_cost
    (countedMatrixZip (·+·) (countedGeneralInverse S.covariance).1
      (countedMatrixScale (2*(lam*lam))
        (countedMatrixMul (rationalColumn g) (rationalColumn g)ᵀ).1).1).1
  simp only [countedTiltMatrices,countedMatrixMul_cost,countedMatrixScale_cost,countedMatrixZip_cost]
  nlinarith

def countedTiltMeanFrom {d : ℕ} (roundCost p : ℕ)
    (P V : Matrix (Fin d) (Fin d) ℚ) (mean : Fin d→ℚ) (lam : ℚ) (g w : Fin d→ℚ) :=
  let base:=countedMatrixMul P (rationalColumn mean)
  let linear:=countedMatrixScale lam (rationalColumn g)
  let subtract:=countedMatrixZip (·-·) base.1 linear.1
  let dot:=countedDot (List.ofFn (fun i=>(g i,w i)))
  let scalar : ℚ×ℕ := (2*(lam*lam)*dot.1,3)
  let correction:=countedMatrixScale scalar.1 (rationalColumn g)
  let rhs:=countedMatrixZip (·+·) subtract.1 correction.1
  let raw:=countedMatrixMul V rhs.1
  let rounded:=countedMatrixUnary (dyadicCeil p) roundCost raw.1
  (fun i=>rounded.1 i 0,
    base.2+linear.2+subtract.2+dot.2+scalar.2+correction.2+rhs.2+raw.2+rounded.2)

theorem countedTiltMeanFrom_value {d : ℕ} (roundCost p : ℕ)
    (P V : Matrix (Fin d) (Fin d) ℚ) (mean : Fin d→ℚ) (lam : ℚ) (g w : Fin d→ℚ) :
    (countedTiltMeanFrom roundCost p P V mean lam g w).1=
      rationalVectorRound p (V*ᵥ (P*ᵥ mean-lam • g+(2*lam^2*(g ⬝ᵥ w)) • g)) := by
  simp only [countedTiltMeanFrom,countedMatrixUnary_value,countedMatrixMul_value,
    countedMatrixScale_value,countedMatrixZip_sub,countedMatrixZip_add,countedDot_spec,
    List.map_ofFn,List.sum_ofFn,←pow_two]
  ext i
  simp only [rationalVectorRound,Matrix.mul_apply,rationalColumn,
    Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct]
  rfl

theorem countedTiltMeanFrom_cost {d : ℕ} (roundCost p : ℕ)
    (P V : Matrix (Fin d) (Fin d) ℚ) (mean : Fin d→ℚ) (lam : ℚ) (g w : Fin d→ℚ) :
    (countedTiltMeanFrom roundCost p P V mean lam g w).2=4*d^2+(6+roundCost)*d+3 := by
  simp only [countedTiltMeanFrom,countedMatrixUnary_cost,countedMatrixMul_cost,
    countedMatrixScale_cost,countedMatrixZip_cost,countedDot_spec,List.length_ofFn]
  ring

/-- `roundCost` and `projectionCost` charge the explicitly identified
rounding and projection primitives. All other scalar operations are counted
in the executed matrix kernels. -/
def countedHistoryStep {d : ℕ} (roundCost projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) : RationalHistoryData d×ℕ :=
  let tilt:=countedTiltMatrices S lam g
  let clip:=countedSpectralClip cfg.dimensionLog cfg.spectralLog cfg.accuracy roundCost
    cfg.smoothing cfg.lowerThreshold cfg.upperThreshold tilt.1.2
  let C:=countedMatrixUnary (dyadicCeil cfg.storagePrecision) roundCost clip.1
  let invC:=countedGeneralInverse C.1
  let B:=countedMatrixUnary (dyadicCeil cfg.storagePrecision) roundCost invC.1
  let mean:=countedTiltMeanFrom roundCost cfg.storagePrecision tilt.1.1 tilt.1.2 S.mean lam g w
  let projected:=Vector.ofFn (oracle B.1 mean.1 cfg.projectionPrecision)
  (⟨fun j=>projected.get j,C.1⟩,
    tilt.2+clip.2+C.2+invC.2+B.2+mean.2+projectionCost)

def historyStepCostBound (d roundCost projectionCost : ℕ) (cfg : RationalHistoryParameters) : ℕ :=
  (2*matrixSqrtIterations cfg.dimensionLog cfg.spectralLog cfg.accuracy*(16+roundCost)+84+3*roundCost)*d^3+
    2*cfg.spectralLog+projectionCost

theorem countedHistoryStep_cost {d : ℕ} (hd : 0<d) (roundCost projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) :
    (countedHistoryStep roundCost projectionCost oracle cfg S lam g w).2≤
      historyStepCostBound d roundCost projectionCost cfg := by
  have ht:=countedTiltMatrices_cost S lam g
  have hc:=countedSpectralClip_cost hd cfg.dimensionLog cfg.spectralLog cfg.accuracy roundCost
    cfg.smoothing cfg.lowerThreshold cfg.upperThreshold (countedTiltMatrices S lam g).1.2
  have hi:=countedGeneralInverse_cost
    (countedMatrixUnary (dyadicCeil cfg.storagePrecision) roundCost
      (countedSpectralClip cfg.dimensionLog cfg.spectralLog cfg.accuracy roundCost
        cfg.smoothing cfg.lowerThreshold cfg.upperThreshold (countedTiltMatrices S lam g).1.2).1).1
  simp only [countedHistoryStep,countedMatrixUnary_cost,countedTiltMeanFrom_cost,historyStepCostBound]
  have hd2 : d*d≤d*d*d := by nlinarith
  have hd1 : d≤d*d*d := by nlinarith
  have hd3 : 1≤d*d*d := by nlinarith
  have hr2 := Nat.mul_le_mul_left roundCost hd2
  have hr1 := Nat.mul_le_mul_left roundCost hd1
  nlinarith

theorem countedMatrixRound_value {d : ℕ} (p roundCost : ℕ)
    (A : Matrix (Fin d) (Fin d) ℚ) :
    (countedMatrixUnary (dyadicCeil p) roundCost A).1=roundRationalMatrix p A :=
  countedMatrixUnary_value _ _ A

theorem countedHistoryStep_value {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (roundCost projectionCost : ℕ) (oracle : RationalProjectionProcedure d)
    (hspec : RationalProjectionSpec W oracle) (cfg : RationalHistoryParameters)
    (lo hi : ℝ) (hlo : 0<lo) (hhi : 0<hi) (hguard : UniformHistoryGuards d cfg lo hi)
    (S : RationalHistoryData d) (hS : RationalHistoryInvariant W lo hi S)
    (lam : ℚ) (g w : Fin d→ℚ) :
    (countedHistoryStep roundCost projectionCost oracle cfg S lam g w).1=
      rationalHistoryStep oracle cfg S lam g w := by
  have ht:=countedTiltMatrices_value S hS.covariance_pos lam g
  obtain ⟨U,c,hC,hc⟩:=rationalTiltCovariance_spectrum S hS.covariance_pos lo hi hlo hhi
    hS.covariance_lower hS.covariance_upper lam g
  have hu:=spectralClipNewton_units hd cfg.dimensionLog cfg.spectralLog cfg.accuracy
    hguard.dimension cfg.smoothing cfg.lowerThreshold cfg.upperThreshold hguard.smoothing_pos
    (rationalMatrixInverse (rationalTiltPrecision S lam g)) U c hC hguard.smoothing_lower
    (fun j=>hguard.lower_spectral (c j) (hc j).1.le (hc j).2)
    (fun j=>hguard.upper_spectral (c j) (hc j).1.le (hc j).2)
  have hclip:=countedSpectralClip_value cfg.dimensionLog cfg.spectralLog cfg.accuracy roundCost
    cfg.smoothing cfg.lowerThreshold cfg.upperThreshold
    (rationalMatrixInverse (rationalTiltPrecision S lam g)) hu
  have hs:=rationalHistoryStep_preserves hd W oracle hspec cfg lo hi hlo hhi hguard S hS lam g w
  have hpos : (realMatrix (rationalNextCovariance cfg S lam g)).PosDef := hs.covariance_pos
  have hi:=countedGeneralInverse_correct (rationalNextCovariance cfg S lam g)
    (realMatrix_unit_reflect _ hpos.isUnit)
  rw [←rationalMatrixInverse_eq_inv] at hi
  simp only [countedHistoryStep,ht,hclip,countedMatrixRound_value,countedTiltMeanFrom_value]
  rw [←rationalNextCovariance,hi]
  simp [Vector.get,rationalHistoryStep,rationalProjectionMetric,rationalTiltMean]

end Paper254
#print axioms Paper254.countedHistoryStep_cost
#print axioms Paper254.countedHistoryStep_value
