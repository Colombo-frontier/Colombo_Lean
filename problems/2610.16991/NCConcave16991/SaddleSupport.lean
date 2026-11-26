import NCConcave16991.DualRegularization
import Mathlib.Analysis.Calculus.Deriv.AffineMap

/-! # First-order support inequalities for actual strongly convex/concave functions -/

open Set InnerProductSpace
open scoped InnerProductSpace

namespace NCConcave16991

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A differentiable strongly convex function has its sharp quadratic support
inequality, even at the boundary of its convex domain. -/
theorem strongConvex_gradient_support {s : Set E} {f : E → ℝ} {m : ℝ} {x y g : E}
    (hf : StrongConvexOn s m f) (hx : x ∈ s) (hy : y ∈ s)
    (hg : HasGradientAt f g x) :
    f x + ⟪g, y - x⟫_ℝ + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  let A : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hA : HasDerivAt A (y - x) 0 := AffineMap.hasDerivAt_lineMap
  have hg0 : HasGradientAt f g (A 0) := by simpa [A] using hg
  have hdf := hg0.hasFDerivAt.comp_hasDerivAt 0 hA
  have hdn := hA.norm_sq
  have hH := hdf.sub (hdn.const_mul (m / 2))
  have hconv := (strongConvexOn_iff_convex.mp hf).comp_affineMap A
  have h0 : (0 : ℝ) ∈ A ⁻¹' s := by simpa [A] using hx
  have h1 : (1 : ℝ) ∈ A ⁻¹' s := by simpa [A] using hy
  have hs := hconv.le_slope_of_hasDerivAt h0 h1 (by norm_num : (0 : ℝ) < 1) hH
  have hs' : ⟪g, y - x⟫_ℝ - m * ⟪x, y - x⟫_ℝ ≤
      (f y - m / 2 * ‖y‖ ^ 2) - (f x - m / 2 * ‖x‖ ^ 2) := by
    simp [A, Function.comp_apply, slope] at hs
    nlinarith only [hs]
  rw [norm_sub_sq_real]
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at hs' ⊢
  have hi := real_inner_comm x y
  rw [hi]
  nlinarith only [hs']

theorem strongConcave_gradient_support {s : Set E} {f : E → ℝ} {m : ℝ} {x y g : E}
    (hf : StrongConcaveOn s m f) (hx : x ∈ s) (hy : y ∈ s)
    (hg : HasGradientAt f g x) :
    f y ≤ f x + ⟪g, y - x⟫_ℝ - m / 2 * ‖y - x‖ ^ 2 := by
  have hneg : StrongConvexOn s m (fun u => -f u) := by
    rw [strongConvexOn_iff_convex]
    have hh := (strongConcaveOn_iff_convex.mp hf).neg
    convert hh using 1
    ext u
    simp only [Pi.neg_apply]
    ring
  have hgneg : HasGradientAt (fun u => -f u) (-g) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hg.hasFDerivAt.neg using 1 <;> first
      | rfl
      | simp only [map_neg]
  have hs := strongConvex_gradient_support hneg hx hy hgneg
  simp only [inner_neg_left] at hs
  linarith

/-- The derivative of the actual scaled squared distance, used for both
proximal primal curvature and dual regularization. -/
theorem scaled_sqDistance_hasGradientAt (a : ℝ) (c x : E) :
    HasGradientAt (fun u : E => a * ‖u - c‖ ^ 2) ((2 * a) • (x - c)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd : HasFDerivAt (fun u : E => u - c) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const c
  have hp := hd.norm_sq.const_smul a
  have he : toDual ℝ E ((2 * a) • (x - c)) =
      a • ((2 : ℕ) • (innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ E)) := by
    ext u
    simp [real_inner_smul_left, two_nsmul]
    ring
  rw [he]
  convert hp using 1 <;> rfl

end NCConcave16991
