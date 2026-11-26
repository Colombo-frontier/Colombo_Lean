import SpectralBasisInvariant254

noncomputable section
open scoped BigOperators Matrix
open Matrix
namespace Paper254

/-- The dense spectral model explicitly exposes the eigensystem operation.
The interface does not include a history update, a linear solve, or projection. -/
structure ExactSpectralPrimitive (d : ℕ) where
  run : (A : Precision d)→A.PosDef→
    (Matrix.unitaryGroup (Fin d) ℝ×Coordinates d)×ℕ
  value : ∀ A hA,A=rotatedPrecision (run A hA).1.1 (run A hA).1.2
  eigen_pos : ∀ A hA j,0<(run A hA).1.2 j
  bound : ℕ
  cost : ∀ A hA,(run A hA).2≤bound

structure RankOneFloorData (d : ℕ) where
  basis : Matrix.unitaryGroup (Fin d) ℝ
  spectrum : Coordinates d
  floored : Precision d

def canonicalRankOneFloor {d : ℕ} (P : PrecisionGaussian d)
    (theta : ℝ) (htheta : 0≤theta) (g : Coordinates d) (q : ℝ) : RankOneFloorData d :=
  let hA := rankOnePrecision_posDef P.positive theta htheta g
  let U := star hA.isHermitian.eigenvectorUnitary
  let c := hA.isHermitian.eigenvalues
  ⟨U,c,rotatedPrecision U (fun j=>min (c j) (1/q))⟩

/-- This is precisely the conditional complete spectral-update primitive:
rank-one precision update, eigensystem, capping, and reconstruction. It
does not perform the mean update or the projection. -/
structure ExactRankOneFloorPrimitive (d : ℕ) where
  run : (P : PrecisionGaussian d)→(theta : ℝ)→0≤theta→Coordinates d→ℝ→RankOneFloorData d×ℕ
  value : ∀ P theta htheta g q,rankOnePrecision P.precision theta g=
    rotatedPrecision (run P theta htheta g q).1.basis (run P theta htheta g q).1.spectrum
  eigen_pos : ∀ P theta htheta g q j,0<(run P theta htheta g q).1.spectrum j
  floor : ∀ P theta htheta g q,(run P theta htheta g q).1.floored=
    rotatedPrecision (run P theta htheta g q).1.basis
      (fun j=>min ((run P theta htheta g q).1.spectrum j) (1/q))
  bound : ℕ
  cost : ∀ P theta htheta g q,(run P theta htheta g q).2≤bound

def countedRealRankOne {d : ℕ} (A : Precision d) (theta : ℝ) (g : Coordinates d) :=
  countedRealMatrix (fun i j=>(A i j+theta*g i*g j,3))

theorem countedRealRankOne_value {d : ℕ} (A : Precision d) (theta : ℝ) (g : Coordinates d) :
    (countedRealRankOne A theta g).1=rankOnePrecision A theta g := by
  rw [countedRealRankOne,countedRealMatrix_value]
  ext i j
  simp [rankOnePrecision,Matrix.vecMulVec,mul_assoc]

theorem countedRealRankOne_cost {d : ℕ} (A : Precision d) (theta : ℝ) (g : Coordinates d) :
    (countedRealRankOne A theta g).2=3*d^2 := by
  rw [countedRealRankOne,countedRealMatrix_cost _ (by intros; rfl)]
  ring

def countedRealFloor {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (q : ℝ) : Precision d×ℕ :=
  let qi := 1/q
  let cap := countedRealVector (fun i=>(min (c i) qi,1))
  let diagonalProduct := countedRealMatrix (fun i j=>(cap.1 i*(U : Precision d) i j,1))
  let result := countedRealMul (U : Precision d)ᴴ diagonalProduct.1
  (result.1,1+cap.2+diagonalProduct.2+result.2)

theorem countedRealFloor_value {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (q : ℝ) :
    (countedRealFloor U c q).1=rotatedPrecision U (fun i=>min (c i) (1/q)) := by
  simp only [countedRealFloor,countedRealMul_value,countedRealMatrix_value,countedRealVector_value]
  have hd : (fun i j=>min (c i) (1/q)*(U : Precision d) i j)=
      Matrix.diagonal (fun i=>min (c i) (1/q))*(U : Precision d) := by
    ext i j; simp [Matrix.diagonal_mul]
  rw [hd,rotatedPrecision,Matrix.mul_assoc]

theorem countedRealFloor_cost {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (q : ℝ) :
    (countedRealFloor U c q).2=2*d^3+d^2+d+1 := by
  simp [countedRealFloor,countedRealMul_cost,countedRealMatrix,countedRealVector,
    Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]
  ring

def countedDenseRankOneFloor {d : ℕ} (spectral : ExactSpectralPrimitive d)
    (P : PrecisionGaussian d) (theta : ℝ) (htheta : 0≤theta) (g : Coordinates d) (q : ℝ) :
    RankOneFloorData d×ℕ :=
  let A := countedRealRankOne P.precision theta g
  have hA : A.1.PosDef := by
    dsimp [A]; rw [countedRealRankOne_value]
    exact rankOnePrecision_posDef P.positive theta htheta g
  let eig := spectral.run A.1 hA
  let floor := countedRealFloor eig.1.1 eig.1.2 q
  (⟨eig.1.1,eig.1.2,floor.1⟩,A.2+eig.2+floor.2)

theorem countedDenseRankOneFloor_value {d : ℕ} (spectral : ExactSpectralPrimitive d)
    (P : PrecisionGaussian d) (theta : ℝ) (htheta : 0≤theta) (g : Coordinates d) (q : ℝ) :
    let out := (countedDenseRankOneFloor spectral P theta htheta g q).1
    rankOnePrecision P.precision theta g=rotatedPrecision out.basis out.spectrum ∧
      (∀ j,0<out.spectrum j) ∧ out.floored=
        rotatedPrecision out.basis (fun j=>min (out.spectrum j) (1/q)) := by
  dsimp only [countedDenseRankOneFloor]
  refine ⟨?_,?_,countedRealFloor_value _ _ _⟩
  · exact (countedRealRankOne_value P.precision theta g).symm.trans (spectral.value _ _)
  · exact spectral.eigen_pos _ _

theorem countedDenseRankOneFloor_cost {d : ℕ} (spectral : ExactSpectralPrimitive d)
    (P : PrecisionGaussian d) (theta : ℝ) (htheta : 0≤theta) (g : Coordinates d) (q : ℝ) :
    (countedDenseRankOneFloor spectral P theta htheta g q).2≤
      2*d^3+4*d^2+d+1+spectral.bound := by
  dsimp only [countedDenseRankOneFloor]
  rw [countedRealRankOne_cost,countedRealFloor_cost]
  have hh := spectral.cost (countedRealRankOne P.precision theta g).1
    (by rw [countedRealRankOne_value]; exact rankOnePrecision_posDef P.positive theta htheta g)
  omega

def denseRankOneFloorPrimitive {d : ℕ} (spectral : ExactSpectralPrimitive d) :
    ExactRankOneFloorPrimitive d where
  run := countedDenseRankOneFloor spectral
  value := fun P theta htheta g q=>(countedDenseRankOneFloor_value spectral P theta htheta g q).1
  eigen_pos := fun P theta htheta g q=>(countedDenseRankOneFloor_value spectral P theta htheta g q).2.1
  floor := fun P theta htheta g q=>(countedDenseRankOneFloor_value spectral P theta htheta g q).2.2
  bound := 2*d^3+4*d^2+d+1+spectral.bound
  cost := countedDenseRankOneFloor_cost spectral

end Paper254
#print axioms Paper254.countedDenseRankOneFloor_value
#print axioms Paper254.countedDenseRankOneFloor_cost
