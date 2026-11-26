import Nonsmooth.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A Fréchet derivative supports a convex function even at a boundary point of its convex domain. -/
theorem convex_first_order {s : Set E} {f : E → ℝ} (hf : ConvexOn ℝ s f)
    {x z : E} (hx : x ∈ s) (hz : z ∈ s) {f' : E →L[ℝ] ℝ} (hd : HasFDerivAt f f' x) :
    f' (z - x) ≤ f z - f x := by
  have hl := hf.comp_affineMap (AffineMap.lineMap x z)
  have h0 : (0 : ℝ) ∈ (AffineMap.lineMap x z) ⁻¹' s := by simpa using hx
  have h1 : (1 : ℝ) ∈ (AffineMap.lineMap x z) ⁻¹' s := by simpa using hz
  have hder : HasDerivAt (f ∘ (AffineMap.lineMap x z : ℝ →ᵃ[ℝ] E)) (f' (z - x)) (0 : ℝ) :=
    hd.comp_hasDerivAt_of_eq (0 : ℝ) AffineMap.hasDerivAt_lineMap (by simp)
  have hh := hl.le_slope_of_hasDerivAt h0 h1 (by norm_num) hder
  simpa [slope_def_field] using hh

/-- The quadratic correction and its derivative yield the full strong-convex tangent inequality. -/
theorem strong_first_order {s : Set E} {μ : ℝ} {f : E → ℝ} (hf : StrongConvexOn s μ f)
    {x z : E} (hx : x ∈ s) (hz : z ∈ s) {f' : E →L[ℝ] ℝ} (hd : HasFDerivAt f f' x) :
    f' (z - x) + μ / 2 * ‖z - x‖ ^ 2 ≤ f z - f x := by
  have hc := strongConvexOn_iff_convex.mp hf
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (μ / 2)
  have h := convex_first_order hc hx hz (hd.sub hn)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat] at h
  change f' (z - x) - μ / 2 * (2 * inner ℝ x (z - x)) ≤
    f z - μ / 2 * ‖z‖ ^ 2 - (f x - μ / 2 * ‖x‖ ^ 2) at h
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at h
  rw [norm_sub_sq_real z x, real_inner_comm]
  nlinarith

theorem strong_gradient_inequality {s : Set E} {μ : ℝ} {f : E → ℝ}
    (hf : StrongConvexOn s μ f) {x z g : E} (hx : x ∈ s) (hz : z ∈ s)
    (hd : HasFDerivAt f (innerSL ℝ g) x) :
    f x - f z ≤ inner ℝ g (x - z) - μ / 2 * ‖x - z‖ ^ 2 := by
  have h := strong_first_order hf hx hz hd
  change inner ℝ g (z - x) + μ / 2 * ‖z - x‖ ^ 2 ≤ f z - f x at h
  rw [inner_sub_right] at h
  rw [norm_sub_rev z x] at h
  rw [inner_sub_right]
  linarith

end
end Nonsmooth
