import Nonsmooth.Geometry

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Feasible (E : Type*) [NormedAddCommGroup E] (R : ℝ) := {x : E // ‖x‖ ≤ R}

def minimumValue (R : ℝ) (f : E → ℝ) : ℝ := sInf {v : ℝ | ∃ x : E, ‖x‖ ≤ R ∧ f x = v}

theorem minimumValue_eq {R : ℝ} {f : E → ℝ} {x : E} (hx : ‖x‖ ≤ R)
    (hm : ∀ y, ‖y‖ ≤ R → f x ≤ f y) : minimumValue R f = f x := by
  apply IsLeast.csInf_eq
  refine ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro v ⟨y, hy, rfl⟩
  exact hm y hy

end
end Nonsmooth
