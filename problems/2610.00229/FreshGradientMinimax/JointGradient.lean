import FreshGradientMinimax.Objective

/-! Recover the two actual partial gradients from a jointly differentiable
scalar function. Joint differentiability is an explicit premise. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

theorem joint_hasFDerivAt_gradient {dx dy : ℕ} {f : Euclid dx → Euclid dy → ℝ}
    {x : Euclid dx} {y : Euclid dy}
    (hf : DifferentiableAt ℝ (fun z : Joint dx dy => f z.1 z.2) (x, y)) :
    HasFDerivAt (fun z : Joint dx dy => f z.1 z.2)
      ((innerSL ℝ (gradient (fun v => f v y) x)).coprod (innerSL ℝ (gradient (f x) y))) (x, y) := by
  let A := fderiv ℝ (fun z : Joint dx dy => f z.1 z.2) (x, y)
  have hd : HasFDerivAt (fun z : Joint dx dy => f z.1 z.2) A (x, y) := hf.hasFDerivAt
  have hx := hd.comp x ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const y x))
  have hy := hd.comp y ((hasFDerivAt_const (𝕜 := ℝ) x y).prodMk (hasFDerivAt_id y))
  have hex := hx.unique hx.differentiableAt.hasGradientAt.hasFDerivAt
  have hey := hy.unique hy.differentiableAt.hasGradientAt.hasFDerivAt
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  have h1 := congrArg (fun B : Euclid dx →L[ℝ] ℝ => B v.1) hex
  have h2 := congrArg (fun B : Euclid dy →L[ℝ] ℝ => B v.2) hey
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, InnerProductSpace.toDual_apply,
    innerSL_apply] at h1 h2
  change A v = ⟪gradient (fun a => f a y) x, v.1⟫_ℝ + ⟪gradient (f x) y, v.2⟫_ℝ
  calc
    A v = A (v.1, 0) + A (0, v.2) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    _ = _ := congrArg₂ (· + ·) h1 h2

end FreshGradientMinimax
