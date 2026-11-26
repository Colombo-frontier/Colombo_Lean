import FreshGradientMinimax.PartialGradientRegularity

/-! Equality near a joint query determines both actual partial gradients. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open Filter Topology

theorem actualJointGradient_eventuallyEq {dx dy : ℕ} {f g : Euclid dx → Euclid dy → ℝ}
    {z : Joint dx dy}
    (h : (fun w : Joint dx dy => f w.1 w.2) =ᶠ[𝓝 z] (fun w => g w.1 w.2)) :
    actualJointGradient f z = actualJointGradient g z := by
  apply Prod.ext
  · have hx : Tendsto (fun x : Euclid dx => (x, z.2)) (𝓝 z.1) (𝓝 z) :=
      continuousAt_id.prodMk continuousAt_const
    have he := (h.comp_tendsto hx).fderiv_eq (𝕜 := ℝ)
    change gradient (fun x => f x z.2) z.1 = gradient (fun x => g x z.2) z.1
    simpa only [gradient] using congrArg (fun C => (InnerProductSpace.toDual ℝ (Euclid dx)).symm C) he
  · have hy : Tendsto (fun y : Euclid dy => (z.1, y)) (𝓝 z.2) (𝓝 z) :=
      continuousAt_const.prodMk continuousAt_id
    have he := (h.comp_tendsto hy).fderiv_eq (𝕜 := ℝ)
    change gradient (f z.1) z.2 = gradient (g z.1) z.2
    simpa only [gradient] using congrArg (fun C => (InnerProductSpace.toDual ℝ (Euclid dy)).symm C) he

end FreshGradientMinimax
