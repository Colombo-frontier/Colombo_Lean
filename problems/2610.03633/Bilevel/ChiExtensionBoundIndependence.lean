import Bilevel.ChiExtensionLowerRegularity

/-! The actual inverse, partial conjugate and lower scalar objective do
not depend on which valid Hessian/Lipschitz bound certifies the construction. -/
noncomputable section
namespace Bilevel.PartialLegendre
open PrimitiveGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem solution_bound_independent {a b : NNReal} (ha : a < 1) (hb : b < 1)
    {G : E → E} (hGa : LipschitzWith a G) (hGb : LipschitzWith b G) (y : E) :
    solution ha hGa y=solution hb hGb y :=
  solution_of_equation hb hGb y (solution ha hGa y) (solution_equation ha hGa y)

theorem conjugate_bound_independent {a b : NNReal} (ha : a < 1) (hb : b < 1)
    {G : E → E} (hGa : LipschitzWith a G) (hGb : LipschitzWith b G) (P : E → ℝ) (y : E) :
    conjugate ha hGa P y=conjugate hb hGb P y := by
  unfold conjugate
  rw [solution_bound_independent ha hb hGa hGb]

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace X] in
theorem jointConjugate_bound_independent {a b : NNReal} (ha : a < 1) (hb : b < 1)
    {G : Joint X Y → Joint X Y} (hGa : LipschitzWith a G) (hGb : LipschitzWith b G)
    (P : Joint X Y → ℝ) (q : Joint X Y) :
    jointConjugate hGa ha P q=jointConjugate hGb hb P q :=
  conjugate_bound_independent ha hb (jointSlice_lipschitz hGa q.fst)
    (jointSlice_lipschitz hGb q.fst) _ q.snd

end Bilevel.PartialLegendre

namespace Bilevel.ChiExtension
open PrimitiveGeometry PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem extensionLower_bound_independent (f : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f)
    (a b : NNReal) (hfa : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (a:ℝ))
    (hfb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (b:ℝ)) (ha : a < 1) (hb : b < 1)
    (m c : ℝ) (x : X) (v : U) (y : Joint U V) :
    extensionLower f hf a hfa ha m c x v y=extensionLower f hf b hfb hb m c x v y := by
  unfold extensionLower jointNormalLower
  rw [jointConjugate_bound_independent ha hb (reassociated_gradient_lipschitz hf a hfa)
    (reassociated_gradient_lipschitz hf b hfb)]

theorem fullExtensionLower_bound_independent (f : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f)
    (a b : NNReal) (hfa : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (a:ℝ))
    (hfb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (b:ℝ)) (ha : a < 1) (hb : b < 1) (μ L : ℝ) :
    fullExtensionLower f hf a hfa ha μ L=fullExtensionLower f hf b hfb hb μ L :=
  funext (fun q => extensionLower_bound_independent f hf a b hfa hfb ha hb (3*μ/2) (L/4) q.fst.fst q.fst.snd q.snd)

end Bilevel.ChiExtension
