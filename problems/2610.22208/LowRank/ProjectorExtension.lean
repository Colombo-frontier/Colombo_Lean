import LowRank.MeasurableRankOne

/-! Adjoin one vector to the image of an orthogonal projector. The formula
uses a zero-safe rank-one update and is measurable in both inputs. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def extendProjector {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (z : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := P + rankOneProjector ((1 - P) *ᵥ z)

theorem projector_mul_residual_eq_zero {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (z : Fin d → ℝ) :
    P *ᵥ ((1 - P) *ᵥ z) = 0 := by
  rw [Matrix.mulVec_mulVec]
  have h : P * (1 - P) = 0 := by noncomm_ring [hP.idempotent]
  rw [h, Matrix.zero_mulVec]

theorem projector_mul_update_eq_zero {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (z : Fin d → ℝ) :
    P * rankOneProjector ((1 - P) *ᵥ z) = 0 :=
  mul_rankOneProjector_eq_zero P _ (projector_mul_residual_eq_zero hP z)

theorem update_mul_projector_eq_zero {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (z : Fin d → ℝ) :
    rankOneProjector ((1 - P) *ᵥ z) * P = 0 := by
  have h := congrArg Matrix.transpose (projector_mul_update_eq_zero hP z)
  simpa only [Matrix.transpose_mul, rankOneProjector_symmetric, hP.symmetric,
    Matrix.transpose_zero] using h

theorem extendProjector_isProjector {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (z : Fin d → ℝ) :
    IsOrthogonalProjector (extendProjector P z) := by
  constructor
  · simp only [extendProjector, Matrix.transpose_add, hP.symmetric, rankOneProjector_symmetric]
  · simp only [extendProjector, add_mul, mul_add, hP.idempotent,
      (rankOneProjector_isProjector _).idempotent,
      projector_mul_update_eq_zero hP z, update_mul_projector_eq_zero hP z, add_zero, zero_add]

theorem extendProjector_mul_original {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (z : Fin d → ℝ) : extendProjector P z * P = P := by
  rw [extendProjector, add_mul, hP.idempotent, update_mul_projector_eq_zero hP z, add_zero]

theorem extendProjector_fixes_original {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (z v : Fin d → ℝ) (hv : P *ᵥ v = v) :
    extendProjector P z *ᵥ v = v := by
  calc
    _ = extendProjector P z *ᵥ (P *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, extendProjector_mul_original hP z, hv]

theorem extendProjector_fixes_new {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (z : Fin d → ℝ) : extendProjector P z *ᵥ z = z := by
  let v := (1 - P) *ᵥ z
  have hz : z = P *ᵥ z + v := by simp only [v, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hEv : extendProjector P z *ᵥ v = v := by
    rw [extendProjector, Matrix.add_mulVec, projector_mul_residual_eq_zero hP z,
      rankOneProjector_fixes, zero_add]
  calc
    _ = extendProjector P z *ᵥ (P *ᵥ z + v) := congrArg (extendProjector P z *ᵥ ·) hz
    _ = P *ᵥ z + v := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, extendProjector_mul_original hP z, hEv]
    _ = z := hz.symm

theorem extendProjector_trace_le {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (z : Fin d → ℝ) : (extendProjector P z).trace ≤ P.trace + 1 := by
  rw [extendProjector, Matrix.trace_add]
  exact add_le_add_left (rankOneProjector_trace_le_one _) _

theorem measurable_extendProjector (d : ℕ) : Measurable
    (fun x : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => extendProjector x.1 x.2) := by
  have hres : Continuous (fun x : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) =>
      (1 - x.1) *ᵥ x.2) := by fun_prop
  have hu := (measurable_rankOneProjector d).comp hres.measurable
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)).add
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hu))

end
end LowRank
