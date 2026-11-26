import Bilevel.PrimitiveQueryModel
import Bilevel.ResponseExistence

/-! The model's retained minimizing response equals the canonical response
used by the verified upper algorithm; no change to the loss or gap occurs. -/
noncomputable section
namespace Bilevel.PrimitiveQuery
set_option autoImplicit false
variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : Instance G μ L ρ Δ R₀ σf σg)

theorem Instance.canonical_response_eq (x : G.X) :
    I.primitive.canonicalResponse.y x=I.response.y x :=
  I.primitive.lower_solution_unique x _ _ (I.primitive.canonicalResponse.minimizes x) (I.response.minimizes x)

theorem Instance.canonical_hyperobjective :
    I.primitive.hyperobjective I.primitive.canonicalResponse=I.primitive.hyperobjective I.response := by
  funext x
  unfold Model.Primitive.hyperobjective
  rw [I.canonical_response_eq]

theorem Instance.canonical_lower_bound (x : G.X) :
    I.gap.floor≤I.primitive.hyperobjective I.primitive.canonicalResponse x := by
  rw [I.canonical_hyperobjective]
  exact I.gap.lower_bound x

theorem Instance.canonical_gap :
    I.primitive.hyperobjective I.primitive.canonicalResponse 0-I.gap.floor≤Δ := by
  rw [I.canonical_hyperobjective]
  exact I.gap.gap

theorem Instance.canonical_initialization :
    ‖(0:G.Y)-I.primitive.canonicalResponse.y 0‖≤R₀ := by
  rw [zero_sub,norm_neg,I.canonical_response_eq]
  exact I.initialization

theorem Instance.loss_eq_canonical (x : G.X) :
    I.loss x=‖gradient (I.primitive.hyperobjective I.primitive.canonicalResponse) x‖ := by
  rw [I.canonical_hyperobjective]
  rfl

theorem Instance.canonical_curvature {Λ : ℝ} (h : I.CurvatureBound Λ) (x y : G.X) :
    ‖gradient (I.primitive.hyperobjective I.primitive.canonicalResponse) x-
      gradient (I.primitive.hyperobjective I.primitive.canonicalResponse) y‖≤Λ*‖x-y‖ := by
  rw [I.canonical_hyperobjective]
  exact h x y

end Bilevel.PrimitiveQuery
