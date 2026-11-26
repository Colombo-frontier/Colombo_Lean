import Bilevel.ModelBridge
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Symmetry of the genuine lower Hessian and of its inverse. -/
noncomputable section
namespace Bilevel.Model.Primitive
open scoped RealInnerProductSpace
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

theorem hessian_symmetric (x : X) (y u v : Y) :
    ⟪P.gyy x y u, v⟫ = ⟪u, P.gyy x y v⟫ := by
  let D : Y →L[ℝ] (Y →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ Y).toContinuousLinearEquiv.toContinuousLinearMap
  have hd : HasFDerivAt (fun z => D (P.gy x z)) (D.comp (P.gyy x y)) y :=
    D.hasFDerivAt.comp y (P.has_gyy x y)
  have h := second_derivative_symmetric
    (fun z => (P.has_gy x z).hasFDerivAt) hd u v
  change ⟪P.gyy x y u, v⟫ = ⟪P.gyy x y v, u⟫ at h
  exact h.trans (real_inner_comm _ _)

theorem hessian_adjoint_eq (x : X) (y : Y) : (P.gyy x y).adjoint = P.gyy x y := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (P.hessian_symmetric x y u v).symm

theorem inverse_adjoint_eq (x : X) (y : Y) (J : Y →L[ℝ] Y)
    (hright : ∀ v, P.gyy x y (J v) = v) : J.adjoint = J := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    ⟪u, J v⟫ = ⟪P.gyy x y (J u), J v⟫ := by rw [hright]
    _ = ⟪J u, P.gyy x y (J v)⟫ := P.hessian_symmetric x y (J u) (J v)
    _ = ⟪J u, v⟫ := by rw [hright]

end Bilevel.Model.Primitive
