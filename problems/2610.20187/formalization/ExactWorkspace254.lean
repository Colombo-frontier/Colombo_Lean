import ExactTotalCost254

noncomputable section
open Matrix
namespace Paper254

/-- Owned-real-cell profiling for the dense spectral implementation.
The primitive workspace parameter covers its internal buffers. Matrix
and vector outputs are materialized; finished temporaries are released. -/
def profiledDenseRankOneFloor {d : ℕ} (spectral : ExactSpectralPrimitive d)
    (spectralWorkspace : ℕ) (P : PrecisionGaussian d) (theta : ℝ)
    (htheta : 0≤theta) (g : Coordinates d) (q : ℝ) :=
  let A := countedRealRankOne P.precision theta g
  have hA : A.1.PosDef := by
    dsimp [A]; rw [countedRealRankOne_value]
    exact rankOnePrecision_posDef P.positive theta htheta g
  let eig := spectral.run A.1 hA
  let floor := countedRealFloor eig.1.1 eig.1.2 q
  ((⟨eig.1.1,eig.1.2,floor.1⟩:RankOneFloorData d),A.2+eig.2+floor.2,
    max (3*d^2+2*d+spectralWorkspace) (8*d^2+4*d+2))

theorem profiledDenseRankOneFloor_program {d : ℕ} (spectral : ExactSpectralPrimitive d)
    (spectralWorkspace : ℕ) (P : PrecisionGaussian d) (theta : ℝ)
    (htheta : 0≤theta) (g : Coordinates d) (q : ℝ) :
    ((profiledDenseRankOneFloor spectral spectralWorkspace P theta htheta g q).1,
      (profiledDenseRankOneFloor spectral spectralWorkspace P theta htheta g q).2.1)=
      countedDenseRankOneFloor spectral P theta htheta g q := rfl

theorem profiledDenseRankOneFloor_workspace {d : ℕ} (spectral : ExactSpectralPrimitive d)
    (spectralWorkspace : ℕ) (P : PrecisionGaussian d) (theta : ℝ)
    (htheta : 0≤theta) (g : Coordinates d) (q : ℝ) :
    (profiledDenseRankOneFloor spectral spectralWorkspace P theta htheta g q).2.2≤
      12*(d+1)^2+spectralWorkspace := by
  simp only [profiledDenseRankOneFloor,max_le_iff]
  constructor <;> nlinarith

/-- A straight-line history update retains a constant number of dense
matrices and vectors. Spectral and projection scratch space are exposed
separately instead of being identified with arithmetic-operation counts. -/
def profiledExactHistory {d : ℕ} {D : ℝ} (W : Domain d D)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (primitiveWorkspace projectionWorkspace : ℕ)
    (P : PrecisionGaussian d) (lam q : ℝ) (hlam : 0≤lam) (hq : 0<q)
    (g w : Coordinates d) : (PrecisionGaussian d×ℕ)×ℕ :=
  let theta := lam*(2*lam)
  have htheta : 0≤theta := mul_nonneg hlam (by positivity)
  let spectral := primitive.run P theta htheta g q
  let b := countedTiltRhs P lam theta g w
  let mean := countedRealSolve spectral.1.basis spectral.1.spectrum b.1
  have hfloor : spectral.1.floored.PosDef := primitive.positive P theta htheta g q hq
  let projected := projection.run spectral.1.floored hfloor mean.1
  ((⟨projected.1,spectral.1.floored,hfloor⟩,2+spectral.2+b.2+mean.2+projected.2),
    max (12*(d+1)^2) (max (3*d^2+3*d+primitiveWorkspace)
      (6*d^2+6*d+projectionWorkspace)))

theorem profiledExactHistory_program {d : ℕ} {D : ℝ} (W : Domain d D)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (primitiveWorkspace projectionWorkspace : ℕ)
    (P : PrecisionGaussian d) (lam q : ℝ) (hlam : 0≤lam) (hq : 0<q)
    (g w : Coordinates d) :
    (profiledExactHistory W primitive projection primitiveWorkspace projectionWorkspace
      P lam q hlam hq g w).1=countedExactHistory W primitive projection P lam q hlam hq g w := rfl

theorem profiledExactHistory_workspace {d : ℕ} {D : ℝ} (W : Domain d D)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (primitiveWorkspace projectionWorkspace : ℕ)
    (P : PrecisionGaussian d) (lam q : ℝ) (hlam : 0≤lam) (hq : 0<q)
    (g w : Coordinates d) :
    (profiledExactHistory W primitive projection primitiveWorkspace projectionWorkspace
      P lam q hlam hq g w).2≤18*(d+1)^2+primitiveWorkspace+projectionWorkspace := by
  simp only [profiledExactHistory,max_le_iff]
  constructor
  · nlinarith
  · constructor <;> nlinarith

theorem profiledExactHistory_dense_workspace {d : ℕ} {D : ℝ} (W : Domain d D)
    (spectral : ExactSpectralPrimitive d) (projection : ExactProjectionPrimitive W)
    (spectralWorkspace projectionWorkspace : ℕ)
    (P : PrecisionGaussian d) (lam q : ℝ) (hlam : 0≤lam) (hq : 0<q)
    (g w : Coordinates d) :
    (profiledExactHistory W (denseRankOneFloorPrimitive spectral) projection
      (12*(d+1)^2+spectralWorkspace) projectionWorkspace P lam q hlam hq g w).2≤
      30*(d+1)^2+spectralWorkspace+projectionWorkspace := by
  have hh := profiledExactHistory_workspace W (denseRankOneFloorPrimitive spectral) projection
    (12*(d+1)^2+spectralWorkspace) projectionWorkspace P lam q hlam hq g w
  nlinarith

/-- Old and next live stores coexist during a sequential update; history
scratch buffers are reused. The two oracle scratch terms are separate. -/
def exactSparseOwnedCells (d N M spectralWorkspace projectionWorkspace : ℕ) :=
  (N+M)*(d^2+d+1)+8*(N+M)+40*(d+1)^2+spectralWorkspace+projectionWorkspace

theorem exactSparseOwnedCells_bound (d N M cap spectralWorkspace projectionWorkspace : ℕ)
    (hN : N≤cap) (hM : M≤cap) :
    exactSparseOwnedCells d N M spectralWorkspace projectionWorkspace≤
      20*cap*(d+1)^2+40*(d+1)^2+spectralWorkspace+projectionWorkspace := by
  unfold exactSparseOwnedCells
  have ha : d^2+d+9≤10*(d+1)^2 := by nlinarith
  have hmul := Nat.mul_le_mul (show N+M≤2*cap by omega) ha
  nlinarith

end Paper254
#print axioms Paper254.profiledExactHistory_program
#print axioms Paper254.profiledExactHistory_dense_workspace
#print axioms Paper254.exactSparseOwnedCells_bound
