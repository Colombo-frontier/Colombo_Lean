import ExactSpectralCost254
import SparseHistoryCost254
import GradientOracle254

noncomputable section
open scoped BigOperators Matrix
open Matrix
namespace Paper254

/-- The specified Mahalanobis projection interface from the manuscript. -/
structure ExactProjectionPrimitive {d : ℕ} {D : ℝ} (W : Domain d D) where
  run : (A : Precision d)→A.PosDef→Coordinates d→Coordinates d×ℕ
  value : ∀ A hA a,(run A hA a).1=
    (metricProject W (precisionFactor hA) (WithLp.toLp 2 a)).val
  bound : ℕ
  cost : ∀ A hA a,(run A hA a).2≤bound

def countedRealSolve {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c b : Coordinates d) : Coordinates d×ℕ :=
  let z := countedRealMatVec (U : Precision d) b
  let y := countedRealVector (fun j=>(z.1 j/c j,1))
  let x := countedRealMatVec (U : Precision d)ᴴ y.1
  (x.1,z.2+y.2+x.2)

theorem countedRealSolve_value {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c b : Coordinates d) (hc : ∀ j,0<c j) :
    (countedRealSolve U c b).1=(rotatedPrecision U c)⁻¹*ᵥb := by
  simp only [countedRealSolve,countedRealMatVec_value,countedRealVector_value]
  exact spectral_solve U c b hc

theorem countedRealSolve_cost {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c b : Coordinates d) : (countedRealSolve U c b).2=4*d^2+d := by
  simp [countedRealSolve,countedRealMatVec_cost,countedRealVector,
    Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]
  ring

def countedTiltRhs {d : ℕ} (P : PrecisionGaussian d)
    (lam theta : ℝ) (g w : Coordinates d) : Coordinates d×ℕ :=
  let s := countedRealDot (List.ofFn (fun j=>(g j,w j)))
  let v := countedRealMatVec P.precision P.mean
  let factor := theta*s.1
  let b := countedRealVector (fun j=>(v.1 j-lam*g j+factor*g j,4))
  (b.1,s.2+v.2+1+b.2)

theorem countedTiltRhs_value {d : ℕ} (P : PrecisionGaussian d)
    (lam theta : ℝ) (g w : Coordinates d) :
    (countedTiltRhs P lam theta g w).1=
      P.precision*ᵥP.mean-lam • g+(theta*(g⬝ᵥw)) • g := by
  ext j
  simp [countedTiltRhs,countedRealVector_value,countedRealMatVec_value,
    countedRealDot_spec,List.map_ofFn,List.sum_ofFn,dotProduct]

theorem countedTiltRhs_cost {d : ℕ} (P : PrecisionGaussian d)
    (lam theta : ℝ) (g w : Coordinates d) :
    (countedTiltRhs P lam theta g w).2=2*d^2+6*d+1 := by
  simp [countedTiltRhs,countedRealMatVec_cost,countedRealDot_spec,
    countedRealVector,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]
  ring

theorem ExactRankOneFloorPrimitive.positive {d : ℕ} (primitive : ExactRankOneFloorPrimitive d)
    (P : PrecisionGaussian d) (theta : ℝ) (htheta : 0≤theta) (g : Coordinates d)
    (q : ℝ) (hq : 0<q) : (primitive.run P theta htheta g q).1.floored.PosDef := by
  rw [primitive.floor]
  exact rotatedPrecision_posDef _ _ (fun j=>lt_min
    (primitive.eigen_pos P theta htheta g q j) (by positivity))

theorem ExactRankOneFloorPrimitive.floor_canonical {d : ℕ} (primitive : ExactRankOneFloorPrimitive d)
    (P : PrecisionGaussian d) (theta : ℝ) (htheta : 0≤theta) (g : Coordinates d) (q : ℝ) :
    (primitive.run P theta htheta g q).1.floored=
      (canonicalRankOneFloor P theta htheta g q).floored := by
  rw [primitive.floor]
  exact spectral_cap_independent (rankOnePrecision P.precision theta g)
    (rankOnePrecision_posDef P.positive theta htheta g) _ _ (primitive.value P theta htheta g q) q

def countedExactHistory {d : ℕ} {D : ℝ} (W : Domain d D)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (P : PrecisionGaussian d) (lam q : ℝ) (hlam : 0≤lam) (hq : 0<q)
    (g w : Coordinates d) : PrecisionGaussian d×ℕ :=
  let theta := lam*(2*lam)
  have htheta : 0≤theta := mul_nonneg hlam (by positivity)
  let spectral := primitive.run P theta htheta g q
  let b := countedTiltRhs P lam theta g w
  let mean := countedRealSolve spectral.1.basis spectral.1.spectrum b.1
  have hfloor : spectral.1.floored.PosDef := primitive.positive P theta htheta g q hq
  let projected := projection.run spectral.1.floored hfloor mean.1
  (⟨projected.1,spectral.1.floored,hfloor⟩,2+spectral.2+b.2+mean.2+projected.2)

theorem countedExactHistory_value {d : ℕ} {D : ℝ} (W : Domain d D)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (P : PrecisionGaussian d) (lam q : ℝ) (hlam : 0≤lam) (hq : 0<q)
    (g w : Coordinates d) :
    (countedExactHistory W primitive projection P lam q hlam hq g w).1=
      P.historyUpdate W lam q hlam hq g w := by
  simp only [countedExactHistory,projection.value]
  have hs := countedRealSolve_value
    (primitive.run P (lam*(2*lam)) (by positivity) g q).1.basis
    (primitive.run P (lam*(2*lam)) (by positivity) g q).1.spectrum
    (countedTiltRhs P lam (lam*(2*lam)) g w).1
    (primitive.eigen_pos P (lam*(2*lam)) (by positivity) g q)
  rw [←primitive.value P (lam*(2*lam)) (by positivity) g q] at hs
  rw [hs,countedTiltRhs_value]
  have congrProject (A B : Precision d) (hA : A.PosDef) (hB : B.PosDef)
      (he : A=B) (a : Coordinates d) :
      (⟨(metricProject W (precisionFactor hA) (WithLp.toLp 2 a)).val,A,hA⟩:PrecisionGaussian d)=
        ⟨(metricProject W (precisionFactor hB) (WithLp.toLp 2 a)).val,B,hB⟩ := by
    cases he; rfl
  exact congrProject _ _ _ _ (primitive.floor_canonical P (lam*(2*lam)) (by positivity) g q) _

theorem countedExactHistory_cost {d : ℕ} {D : ℝ} (W : Domain d D)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (P : PrecisionGaussian d) (lam q : ℝ) (hlam : 0≤lam) (hq : 0<q)
    (g w : Coordinates d) :
    (countedExactHistory W primitive projection P lam q hlam hq g w).2≤
      6*d^2+7*d+3+primitive.bound+projection.bound := by
  dsimp only [countedExactHistory]
  rw [countedTiltRhs_cost,countedRealSolve_cost]
  have hp := primitive.cost P (lam*(2*lam)) (by positivity) g q
  have hproj := projection.cost
    (primitive.run P (lam*(2*lam)) (by positivity) g q).1.floored
    (primitive.positive P (lam*(2*lam)) (by positivity) g q hq)
    (countedRealSolve (primitive.run P (lam*(2*lam)) (by positivity) g q).1.basis
      (primitive.run P (lam*(2*lam)) (by positivity) g q).1.spectrum
      (countedTiltRhs P lam (lam*(2*lam)) g w).1).1
  omega

theorem countedExactHistory_dense_cost {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (spectral : ExactSpectralPrimitive d) (projection : ExactProjectionPrimitive W)
    (P : PrecisionGaussian d) (lam q : ℝ) (hlam : 0≤lam) (hq : 0<q)
    (g w : Coordinates d) :
    (countedExactHistory W (denseRankOneFloorPrimitive spectral) projection P lam q hlam hq g w).2≤
      24*d^3+spectral.bound+projection.bound := by
  apply (countedExactHistory_cost W _ projection P lam q hlam hq g w).trans
  dsimp [denseRankOneFloorPrimitive]
  have hd2 : d≤d^2 := by nlinarith
  have hd3 : d^2≤d^3 := by nlinarith [Nat.mul_le_mul_right (d^2) hd]
  nlinarith

theorem countedExactHistory_quadratic_cost {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (c : ℕ) (hc : primitive.bound≤c*d^2)
    (P : PrecisionGaussian d) (lam q : ℝ) (hlam : 0≤lam) (hq : 0<q)
    (g w : Coordinates d) :
    (countedExactHistory W primitive projection P lam q hlam hq g w).2≤
      (c+16)*d^2+projection.bound := by
  apply (countedExactHistory_cost W primitive projection P lam q hlam hq g w).trans
  have hd2 : d≤d^2 := by nlinarith
  nlinarith

end Paper254
#print axioms Paper254.countedExactHistory_value
#print axioms Paper254.countedExactHistory_dense_cost
#print axioms Paper254.countedExactHistory_quadratic_cost
