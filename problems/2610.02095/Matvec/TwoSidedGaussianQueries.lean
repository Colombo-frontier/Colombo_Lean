import Matvec.TwoSidedGaussianStep

/-! Arbitrary real query vectors, including zero queries, can be replayed from
the extra-exposure row/column record. No normalization or nonzero premise is
needed: query magnitudes are restored by multiplication after inverse rotation. -/

namespace Matvec
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

variable {r s : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

theorem query_rotation_scaled_coordinate
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (u z : Fin (r + 1) → ℝ) :
    ‖(LowRank.basisCoordinates b).symm u‖ *
      LowRank.coordinateRotation b (LowRank.rowGauge b u) z 0 = u ⬝ᵥ z := by
  have h := LowRank.coordinateRotation_dot b (LowRank.rowGauge b u) u z
  simp_rw [LowRank.rowGauge_aligns] at h
  simpa [dotProduct] using h

theorem twoSided_query_scaled_row
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : Fin (r + 1) → ℝ) (w : Fin (s + 1) → ℝ)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    ‖(LowRank.basisCoordinates b).symm u‖ •
        (twoSidedRotate (queryGauge b u) (queryGauge c w) X 0) =
      LowRank.coordinateRotation c (LowRank.rowGauge c w) (Xᵀ *ᵥ u) := by
  rw [twoSided_query_rotation_eq]
  change _ • LowRank.coordinateRotation c (LowRank.rowGauge c w)
    (LowRank.rotateMatrixColumns b (LowRank.rowGauge b u) X 0) = _
  rw [← map_smul]
  congr 1
  funext j
  have h := query_rotation_scaled_coordinate b u (fun i => X i j)
  simpa only [Pi.smul_apply, smul_eq_mul, LowRank.rotateMatrixColumns_apply,
    Matrix.mulVec, Matrix.transpose_apply, dotProduct, mul_comm] using h

theorem twoSided_query_scaled_column
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : Fin (r + 1) → ℝ) (w : Fin (s + 1) → ℝ)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    ‖(LowRank.basisCoordinates c).symm w‖ •
        (fun i => twoSidedRotate (queryGauge b u) (queryGauge c w) X i 0) =
      LowRank.coordinateRotation b (LowRank.rowGauge b u) (X *ᵥ w) := by
  funext i
  rw [twoSided_query_rotation_eq]
  change _ * LowRank.coordinateRotation c (LowRank.rowGauge c w)
    (LowRank.rotateMatrixColumns b (LowRank.rowGauge b u) X i) 0 = _
  rw [query_rotation_scaled_coordinate]
  have h := congrFun (LowRank.rotateMatrixColumns_mulVec b (LowRank.rowGauge b u) X w) i
  simpa only [Matrix.mulVec, dotProduct, mul_comm] using h

def scaledExposedTwoSidedReply
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : Fin (r + 1) → ℝ) (w : Fin (s + 1) → ℝ)
    (record : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) :
    (Fin (r + 1) → ℝ) × (Fin (s + 1) → ℝ) :=
  let reply := exposedTwoSidedReply b c u w record
  (‖(LowRank.basisCoordinates c).symm w‖ • reply.1,
    ‖(LowRank.basisCoordinates b).symm u‖ • reply.2)

/-- Exact replay of an arbitrary real two-sided query, including redundant
and zero residual directions. The extra exposed coordinates are harmless. -/
theorem scaledExposedTwoSidedReply_eq_oracle
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : Fin (r + 1) → ℝ) (w : Fin (s + 1) → ℝ)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    scaledExposedTwoSidedReply b c u w
      (splitTwoSided (twoSidedRotate (queryGauge b u) (queryGauge c w) X)).1 =
      (X *ᵥ w, Xᵀ *ᵥ u) := by
  let Z := twoSidedRotate (queryGauge b u) (queryGauge c w) X
  have hcol : Fin.cons (Z 0 0) (fun i => Z i.succ 0) = fun i => Z i 0 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  apply Prod.ext
  · change _ • LowRank.coordinateRotation b (LowRank.rowGauge b u)
      (Fin.cons (Z 0 0) (fun i => Z i.succ 0)) = _
    rw [hcol, ← map_smul, twoSided_query_scaled_column b c u w X]
    exact LowRank.query_rotation_involutive b u _
  · change _ • LowRank.coordinateRotation c (LowRank.rowGauge c w)
      (twoSidedRotate (queryGauge b u) (queryGauge c w) X 0) = _
    rw [← map_smul, twoSided_query_scaled_row b c u w X]
    exact LowRank.query_rotation_involutive c w _

theorem measurable_scaledExposedTwoSidedReply {S : Type*} [MeasurableSpace S]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F)
    (u : S → Fin (r + 1) → ℝ) (w : S → Fin (s + 1) → ℝ)
    (hu : Measurable u) (hw : Measurable w) :
    Measurable (fun p : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
      scaledExposedTwoSidedReply b c (u p.1) (w p.1) p.2) := by
  have hr := (measurable_exposedTwoSidedReply b c u w hu hw).snd
  have hnu : Measurable (fun p : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
      ‖(LowRank.basisCoordinates b).symm (u p.1)‖) :=
    ((LowRank.basisCoordinates b).symm.continuous.measurable.comp (hu.comp measurable_fst)).norm
  have hnw : Measurable (fun p : S × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
      ‖(LowRank.basisCoordinates c).symm (w p.1)‖) :=
    ((LowRank.basisCoordinates c).symm.continuous.measurable.comp (hw.comp measurable_fst)).norm
  exact (hnw.smul hr.fst).prodMk (hnu.smul hr.snd)

end
end Matvec
