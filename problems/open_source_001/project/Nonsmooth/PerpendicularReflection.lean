import Nonsmooth.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def perpendicularReflection (w x : E) : E := (ℝ ∙ w)ᗮ.reflection x

theorem perpendicularReflection_formula (w x : E) :
    perpendicularReflection w x = -(((2 : ℝ) * (⟪w, x⟫_ℝ / ‖w‖ ^ 2)) • w - x) := by
  simp [perpendicularReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, smul_eq_mul]
  simp only [two_smul, two_mul, add_smul]

theorem perpendicularReflection_zero (x : E) : perpendicularReflection 0 x = x := by
  apply (Submodule.reflection_eq_self_iff x).mpr
  simp only [Submodule.span_zero_singleton, Submodule.bot_orthogonal_eq_top, Submodule.mem_top]

end
end Nonsmooth
