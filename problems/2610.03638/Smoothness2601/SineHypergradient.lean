import Smoothness2601.SineLift
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Genuine vector hypergradients after substituting the unique sine-lift root.
The perturbation estimate is derived from the scalar implicit derivative. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Smoothness2601.SineLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def liftedObjective (a b h : ℝ) (A B : E → ℝ) (x : E) : ℝ :=
  a*(A x+theta ((a/b)/h) (B x))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem liftedObjective_eq_substitution {a b h : ℝ} (hb : b ≠ 0)
    (A B : E → ℝ) (x : E) :
    liftedObjective a b h A B x = a*A x+b*lowerRoot (a/b) h (B x) :=
  (actual_hyperobjective_identity a b (A x) (B x) h hb).symm

theorem theta_comp_hasGradientAt {c : ℝ} (B : E → ℝ) (gB : E → E)
    (hg : ∀ x, HasGradientAt B (gB x) x) (x : E) (hc : |c*B x| < 1) :
    HasGradientAt (fun x => theta c (B x)) (deriv (theta c) (B x) • gB x) x := by
  have hd : HasDerivAt (theta c) (deriv (theta c) (B x)) (B x) :=
    (hasDerivAt_theta hc).differentiableAt.hasDerivAt
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hd.comp_hasFDerivAt x (hg x).hasFDerivAt using 1
  ext v
  simp only [InnerProductSpace.toDual_apply,real_inner_smul_left,
    ContinuousLinearMap.smul_apply,smul_eq_mul]

theorem liftedObjective_hasGradientAt {a b h : ℝ} (A B : E → ℝ) (gA gB : E → E)
    (ha : ∀ x, HasGradientAt A (gA x) x) (hb : ∀ x, HasGradientAt B (gB x) x)
    (x : E) (hc : |((a/b)/h)*B x| < 1) :
    HasGradientAt (liftedObjective a b h A B)
      (a • (gA x+deriv (theta ((a/b)/h)) (B x) • gB x)) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := ((ha x).hasFDerivAt.add (theta_comp_hasGradientAt B gB hb x hc).hasFDerivAt).const_mul a
  simpa only [liftedObjective,map_smul,map_add] using hd

theorem gradient_distortion {a b h B₀ C : ℝ} (ha0 : 0 ≤ a)
    (A B : E → ℝ) (gA gB : E → E)
    (ha : ∀ x, HasGradientAt A (gA x) x) (hb : ∀ x, HasGradientAt B (gB x) x)
    (hB : ∀ x, |B x| ≤ B₀) (hgrad : ∀ x, ‖gB x‖ ≤ C)
    (hc : |(a/b)/h| * B₀ ≤ 1/4) (x : E) :
    ‖gradient (liftedObjective a b h A B) x-a • (gA x+gB x)‖ ≤
      a*(2*((a/b)/h)^2*B₀^2)*C := by
  have hs : |((a/b)/h)*B x| < 1 := by
    have hh := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg ((a/b)/h))
    rw [← abs_mul] at hh
    linarith
  rw [(liftedObjective_hasGradientAt A B gA gB ha hb x hs).gradient]
  have he : a • (gA x+deriv (theta ((a/b)/h)) (B x) • gB x)-a • (gA x+gB x) =
      a • ((deriv (theta ((a/b)/h)) (B x)-1) • gB x) := by
    simp only [smul_add,sub_smul,one_smul,smul_sub]
    abel
  rw [he,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha0]
  have ht := theta_derivative_error (hB x) hc
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul ht (hgrad x) (norm_nonneg _) (by positivity)) ha0).trans_eq (by ring)

theorem lifted_gradient_barrier {a b h B₀ C : ℝ} (ha0 : 0 ≤ a)
    (A B : E → ℝ) (gA gB : E → E)
    (ha : ∀ x, HasGradientAt A (gA x) x) (hb : ∀ x, HasGradientAt B (gB x) x)
    (hB : ∀ x, |B x| ≤ B₀) (hgrad : ∀ x, ‖gB x‖ ≤ C)
    (hc : |(a/b)/h| * B₀ ≤ 1/4) (hsmall : 2*((a/b)/h)^2*B₀^2*C ≤ 1/4)
    (x : E) (hbar : (1/2:ℝ) ≤ ‖gA x+gB x‖) :
    a/4 ≤ ‖gradient (liftedObjective a b h A B) x‖ := by
  have he := gradient_distortion ha0 A B gA gB ha hb hB hgrad hc x
  have ht : ‖a • (gA x+gB x)‖ ≤
      ‖gradient (liftedObjective a b h A B) x‖+
        ‖gradient (liftedObjective a b h A B) x-a • (gA x+gB x)‖ := by
    have hn := norm_sub_le (gradient (liftedObjective a b h A B) x)
      (gradient (liftedObjective a b h A B) x-a • (gA x+gB x))
    simpa only [sub_sub_cancel] using hn
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha0] at ht
  have hb1 := mul_le_mul_of_nonneg_left hbar ha0
  have hb2 := mul_le_mul_of_nonneg_left hsmall ha0
  nlinarith

theorem scaled_hasGradientAt (f : E → ℝ) (g : E → E)
    (hf : ∀ x, HasGradientAt f (g x) x) (scaleFactor : ℝ) (x : E) :
    HasGradientAt (fun x => f (scaleFactor⁻¹ • x)) (scaleFactor⁻¹ • g (scaleFactor⁻¹ • x)) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := (hf (scaleFactor⁻¹ • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul scaleFactor⁻¹)
  convert hd using 1
  ext v
  simp only [InnerProductSpace.toDual_apply,real_inner_smul_left,
    real_inner_smul_right,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply]

end Smoothness2601.SineLift
