import LowRank.GaussianMatrixRows

/-! An explicit measurable orthogonal gauge. Division by zero is total in ℝ,
so the formula is measurable even when the reflecting normal vanishes. -/

namespace LowRank
open MeasureTheory
open scoped InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def householder (w : E) : E ≃ₗᵢ[ℝ] E := (ℝ ∙ w)ᗮ.reflection

theorem householder_apply (w z : E) :
    householder w z = z - (2 * (⟪w, z⟫_ℝ / ‖w‖ ^ 2)) • w := by
  rw [householder, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp [smul_smul, neg_sub, two_smul, two_mul, add_smul]

theorem measurable_householder_eval : Measurable (fun p : E × E => householder p.1 p.2) := by
  simp_rw [householder_apply]
  fun_prop

theorem householder_equal_norm {u v : E} (h : ‖u‖ = ‖v‖) :
    householder (u - v) u = v := Submodule.reflection_sub h

/-- Aligns any vector with a fixed unit axis, without choosing a basis by choice. -/
def alignToAxis (a z : E) : E ≃ₗᵢ[ℝ] E := householder (z - ‖z‖ • a)

theorem alignToAxis_self {a : E} (ha : ‖a‖ = 1) (z : E) :
    alignToAxis a z z = ‖z‖ • a := by
  apply householder_equal_norm
  simp [norm_smul, ha]

theorem measurable_alignToAxis_eval (a : E) :
    Measurable (fun p : E × E => alignToAxis a p.1 p.2) := by
  simp only [alignToAxis, householder_apply]
  fun_prop

theorem alignToAxis_involutive (a z : E) : Function.Involutive (alignToAxis a z) := by
  intro y
  exact Submodule.reflection_reflection _ y

end
end LowRank
