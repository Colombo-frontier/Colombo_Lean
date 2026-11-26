import LowRank.GaussianCoordinates

/-! A total measurable unit-direction map. At a zero residual it selects a
fixed basis axis, allowing fixed-budget simulations to spend a dummy query
while decoding the original reply with coefficient zero. -/

namespace LowRank
open MeasureTheory
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r : ℕ}

def coordinateSize (b : OrthonormalBasis (Fin (r + 1)) ℝ E) (u : Fin (r + 1) → ℝ) : ℝ :=
  ‖(basisCoordinates b).symm u‖

def unitCoordinateDirection (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) : Fin (r + 1) → ℝ :=
  if u = 0 then (basisCoordinates b) (b 0) else (coordinateSize b u)⁻¹ • u

theorem coordinateSize_ne_zero (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) (hu : u ≠ 0) : coordinateSize b u ≠ 0 := by
  apply norm_ne_zero_iff.mpr
  intro hzero
  apply hu
  have h := congrArg (basisCoordinates b) hzero
  simpa using h

theorem unitCoordinateDirection_norm (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) : ‖(basisCoordinates b).symm (unitCoordinateDirection b u)‖ = 1 := by
  unfold unitCoordinateDirection
  split_ifs with hu
  · rw [ContinuousLinearEquiv.symm_apply_apply, b.norm_eq_one]
  · rw [map_smul, norm_smul, norm_inv]
    change ‖‖(basisCoordinates b).symm u‖‖⁻¹ * ‖(basisCoordinates b).symm u‖ = 1
    rw [norm_norm]
    exact inv_mul_cancel₀ (coordinateSize_ne_zero b u hu)

theorem coordinateSize_smul_direction (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : Fin (r + 1) → ℝ) : coordinateSize b u • unitCoordinateDirection b u = u := by
  unfold unitCoordinateDirection
  split_ifs with hu
  · simp [hu, coordinateSize]
  · rw [smul_smul, mul_inv_cancel₀ (coordinateSize_ne_zero b u hu), one_smul]

theorem measurable_coordinateSize (b : OrthonormalBasis (Fin (r + 1)) ℝ E) :
    Measurable (coordinateSize b) := (basisCoordinates b).symm.continuous.measurable.norm

theorem measurable_unitCoordinateDirection (b : OrthonormalBasis (Fin (r + 1)) ℝ E) :
    Measurable (unitCoordinateDirection b) := by
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    ((measurable_coordinateSize b).inv.smul measurable_id)

end
end LowRank
