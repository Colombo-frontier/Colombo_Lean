import Bilevel.ChiQuadraticLower
import Bilevel.GradientJetBounds

/-! An exact-quadratic source Primitive from actual upper and lower scalars.
This adapter also retains the displayed attained response and constant lower
Hessian blocks; it makes no information or query-complexity assumption. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiQuadratic
open PrimitiveGeometry PartialLegendre
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem quadratic_primitive (f : Joint X Y → ℝ) (hf : ContDiff ℝ 3 f)
    (H : Y →L[ℝ] Y) (C : X →L[ℝ] Y)
    (hsym : ∀ u v,⟪H u,v⟫=⟪u,H v⟫)
    (μ Lf Lg Cf : ℝ) (hμ : 0<μ) (hLf : 0≤Lf) (hCf : 0≤Cf)
    (hcoerce : ∀ y,μ*‖y‖^2≤⟪y,H y⟫) (hbudget : ‖H‖+‖C‖≤Lg)
    (hupper : ∀ x y,‖gradient (fun v => f (pack x v)) y‖≤Cf)
    (hjet : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤Lf)
    (response : X → Y) (hresponse : ∀ x,H (response x)=C x) :
    ∃ P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf 0,
      (∀ x y,P.f x y=f (pack x y)) ∧
      (∀ x y,P.g x y=lower H C (pack x y)) ∧
      (∀ x y,P.gy x y=H y-C x) ∧
      (∀ x y,P.gyy x y=H) ∧ (∀ x y,P.gxy x y= -C.adjoint) ∧
      ∃ r : P.Response,(∀ x,r.y x=response x) ∧
        (∀ x,P.hyperobjective r x=f (pack x (response x))) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=response x) := by
  have hg := (lower_contDiff H C 3).differentiable (by norm_num)
  have hK (z : Joint X Y) : HasFDerivAt (gradient (lower H C)) (hessian H C) z := by
    rw [lower_gradient H C hsym]
    exact (hessian H C).hasFDerivAt
  have hLg : 0≤Lg := (add_nonneg (norm_nonneg H) (norm_nonneg C)).trans hbudget
  have hgsmooth (z w : Joint X Y) :
      ‖gradient (lower H C) z-gradient (lower H C) w‖≤Lg*‖z-w‖ := by
    rw [lower_gradient H C hsym,← map_sub]
    exact ((hessian H C).le_opNorm (z-w)).trans
      (mul_le_mul_of_nonneg_right ((hessian_norm_bound H C).trans hbudget) (norm_nonneg _))
  let P := ChiPrimitive.fromFull f (lower H C) (hf.differentiable (by norm_num)) hg
    (fun _ => hessian H C) hK μ Lf Lg Cf 0 hμ hLf hLg hCf le_rfl
    (lower_strong_convex H C hsym hcoerce) hupper
    (GradientJetBounds.gradient_lipschitz hf Lf hjet) hgsmooth
    (by
      intro z w
      rw [sub_self,zero_mul]
      exact (norm_zero (E:=Joint X Y →L[ℝ] Joint X Y)).le)
  have hgy (x : X) (y : Y) : P.gy x y=H y-C x := by
    change (gradient (lower H C) (pack x y)).snd= _
    rw [lower_gradient H C hsym,hessian_apply]
    rfl
  have hyy (x : X) (y : Y) : P.gyy x y=H := by
    ext v
    change H v-C 0=H v
    rw [map_zero,sub_zero]
  have hxy (x : X) (y : Y) : P.gxy x y= -C.adjoint := by
    ext v
    rfl
  let r : P.Response := ⟨response,fun x => P.stationary_minimizes x (response x) (by rw [hgy,hresponse,sub_self])⟩
  refine ⟨P,(fun _ _ => rfl),(fun _ _ => rfl),hgy,hyy,hxy,r,(fun _ => rfl),(fun _ => rfl),?_⟩
  intro x y
  constructor
  · intro hy
    exact P.lower_solution_unique x y (response x) hy (r.minimizes x)
  · rintro rfl
    exact r.minimizes x

end Bilevel.ChiQuadratic
