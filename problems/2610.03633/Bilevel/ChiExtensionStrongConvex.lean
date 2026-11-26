import Bilevel.ChiExtensionLowerRegularity

/-! First-order strong convexity of the actual partial-conjugate lower
objective, with its actual gradient and the prescribed modulus mu. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {δ : NNReal} (hδ : δ < 1) {G : E → E} (hG : LipschitzWith δ G)
  (P : E → ℝ) (hP : ∀ z,HasGradientAt P (G z) z)
include hP

theorem coupledLower_hasGradientAt (m : ℝ) (b y : E) :
    HasGradientAt (coupledLower hδ hG P m b) (m • solution hδ hG y-b) y := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert ((conjugate_hasGradientAt hδ hG P hP y).hasFDerivAt.const_mul m).sub
    ((InnerProductSpace.toDual ℝ E b).hasFDerivAt) using 1
  ext v
  simp [inner_sub_left,real_inner_smul_left]

theorem coupledLower_strong_model {m : ℝ} (hm : 0 ≤ m) (b y w : E) :
    coupledLower hδ hG P m b y+
      ⟪gradient (coupledLower hδ hG P m b) y,w-y⟫+
      m/(2*(1+(δ:ℝ)))*‖w-y‖^2 ≤ coupledLower hδ hG P m b w := by
  rw [(coupledLower_hasGradientAt hδ hG P hP m b y).gradient]
  have hh := mul_le_mul_of_nonneg_left (conjugate_strong_model hδ hG P hP y w) hm
  unfold coupledLower
  simp only [inner_sub_left,real_inner_smul_left,inner_sub_right] at hh ⊢
  ring_nf at hh ⊢
  linarith

end Bilevel.PartialLegendre

namespace Bilevel.ChiExtension
open PrimitiveGeometry PartialLegendre
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem extensionLower_strong_convex (f : Joint (Joint X U) V → ℝ) (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖ ≤ (δ:ℝ)) (hδ : δ < 1)
    (hsmall : (δ:ℝ) ≤ 1/12) {μ : ℝ} (hμ : 0 < μ) (c : ℝ) (x : X) (v : U)
    (y w : Joint U V) :
    extensionLower f hf δ hb hδ (3*μ/2) c x v y+
      ⟪gradient (extensionLower f hf δ hb hδ (3*μ/2) c x v) y,w-y⟫+
      μ/2*‖w-y‖^2 ≤ extensionLower f hf δ hb hδ (3*μ/2) c x v w := by
  let P := reassociate f
  have hP : ∀ z,HasGradientAt P (gradient P z) z :=
    fun z => (((reassociate_contDiff hf).differentiable (by norm_num)) z).hasGradientAt
  have hh := coupledLower_strong_model hδ
    (jointSlice_lipschitz (reassociated_gradient_lipschitz hf δ hb) x)
    (fun z => P (pack x z)) (jointSlice_hasGradientAt P hP x)
    (show 0 ≤ 3*μ/2 by positivity) (pack (c • v) (0:V)) y w
  have hid : extensionLower f hf δ hb hδ (3*μ/2) c x v =
      coupledLower hδ (jointSlice_lipschitz (reassociated_gradient_lipschitz hf δ hb) x)
        (fun z => P (pack x z)) (3*μ/2) (pack (c • v) (0:V)) := by
    funext z
    exact jointNormalLower_slice _ _ _ _ _ _ _ _
  rw [hid]
  have hden : 0 < 2*(1+(δ:ℝ)) := by positivity
  have hm : μ/2 ≤ (3*μ/2)/(2*(1+(δ:ℝ))) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsmall hμ.le]
  exact (add_le_add_left (mul_le_mul_of_nonneg_right hm (sq_nonneg _)) _).trans hh

end Bilevel.ChiExtension
