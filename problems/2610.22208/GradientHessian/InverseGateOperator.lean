import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-! The inverse needed by the numerical gate is constructed from the stated
lower quadratic-form inequality, rather than assumed separately. -/

noncomputable section
namespace GradientHessian.InverseGate

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def LowerBound (A : E →L[ℝ] E) : Prop := ∀ x, ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ

omit [CompleteSpace E] in
theorem lowerBound_norm (A : E →L[ℝ] E) (hA : LowerBound A) (x : E) : ‖x‖ ≤ ‖A x‖ := by
  have h := (hA x).trans (real_inner_le_norm (A x) x)
  by_cases hx : x = 0
  · simp [hx]
  · have hp := norm_pos_iff.mpr hx
    nlinarith

theorem lowerBound_isUnit (A : E →L[ℝ] E) (hA : LowerBound A) : IsUnit A := by
  apply A.isUnit_of_forall_le_norm_inner_map (c := 1) (by norm_num)
  intro x
  simpa only [NNReal.coe_one, mul_one, Real.norm_eq_abs] using
    (hA x).trans (le_abs_self ⟪A x, x⟫_ℝ)

def equivalence (A : E →L[ℝ] E) (hA : LowerBound A) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofUnit (lowerBound_isUnit A hA).unit

@[simp] theorem equivalence_apply (A : E →L[ℝ] E) (hA : LowerBound A) (x : E) :
    equivalence A hA x = A x := by
  change ((lowerBound_isUnit A hA).unit : E →L[ℝ] E) x = A x
  rw [IsUnit.unit_spec]

def inverse (A : E →L[ℝ] E) (hA : LowerBound A) : E →L[ℝ] E :=
  (equivalence A hA).symm.toContinuousLinearMap

@[simp] theorem apply_inverse (A : E →L[ℝ] E) (hA : LowerBound A) (x : E) :
    A (inverse A hA x) = x := by
  have h := (equivalence A hA).apply_symm_apply x
  simpa only [equivalence_apply] using h

@[simp] theorem inverse_apply (A : E →L[ℝ] E) (hA : LowerBound A) (x : E) :
    inverse A hA (A x) = x := by
  have h := (equivalence A hA).symm_apply_apply x
  simpa only [equivalence_apply] using h

theorem inverse_norm_le (A : E →L[ℝ] E) (hA : LowerBound A) (x : E) :
    ‖inverse A hA x‖ ≤ ‖x‖ := by
  simpa only [apply_inverse] using lowerBound_norm A hA (inverse A hA x)

theorem inverse_quadratic_nonneg (A : E →L[ℝ] E) (hA : LowerBound A) (x : E) :
    0 ≤ ⟪x, inverse A hA x⟫_ℝ := by
  have h := hA (inverse A hA x)
  rw [apply_inverse] at h
  exact (sq_nonneg _).trans h

end GradientHessian.InverseGate
