import Bilevel.RadialSecond
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! The quadratic radial wrapper used in 2601, including genuine derivatives
and dimension-free smoothness. The compression itself is reused verbatim. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Smoothness2601.RadialWrapper
open Bilevel.RadialWrapper
variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]

def carried (R : ℝ) (P : E →L[ℝ] Z) (H : Z → ℝ) (w : E) : ℝ :=
  H (P (compress R w))

def carriedGradient (R : ℝ) (P : E →L[ℝ] Z) (g : Z → Z) (w : E) : E :=
  compressDerivative R w (P.adjoint (g (P (compress R w))))

def wrapped (R η : ℝ) (P : E →L[ℝ] Z) (H : Z → ℝ) (w : E) : ℝ :=
  carried R P H w + η/2*‖w‖^2

def wrappedGradient (R η : ℝ) (P : E →L[ℝ] Z) (g : Z → Z) (w : E) : E :=
  carriedGradient R P g w + η • w

theorem carried_hasGradientAt (R : ℝ) (P : E →L[ℝ] Z) (H : Z → ℝ)
    (g : Z → Z) (hg : ∀ z, HasGradientAt H (g z) z) (w : E) :
    HasGradientAt (carried R P H) (carriedGradient R P g w) w := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := (hg (P (compress R w))).hasFDerivAt.comp w
    (P.hasFDerivAt.comp w (compress_hasFDerivAt R w))
  convert hd using 1
  ext v
  simp only [InnerProductSpace.toDual_apply,ContinuousLinearMap.comp_apply,
    carriedGradient,compressDerivative_apply,map_sub,map_smul,inner_sub_left,
    inner_sub_right,real_inner_smul_left,real_inner_smul_right]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    InnerProductSpace.toDual_apply,smul_eq_mul,ContinuousLinearMap.adjoint_inner_left]
  have hi : ⟪w,P.adjoint (g (P (compress R w)))⟫ = ⟪g (P (compress R w)),P w⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact real_inner_comm _ _
  rw [hi]
  ring

theorem quadratic_hasGradientAt (η : ℝ) (w : E) :
    HasGradientAt (fun w : E => η/2*‖w‖^2) (η • w) w := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert ((hasStrictFDerivAt_norm_sq w).hasFDerivAt.const_mul (η/2)) using 1
  ext v
  simp only [InnerProductSpace.toDual_apply,real_inner_smul_left,
    ContinuousLinearMap.smul_apply,smul_eq_mul,innerSL_apply]
  ring

theorem wrapped_hasGradientAt (R η : ℝ) (P : E →L[ℝ] Z) (H : Z → ℝ)
    (g : Z → Z) (hg : ∀ z, HasGradientAt H (g z) z) (w : E) :
    HasGradientAt (wrapped R η P H) (wrappedGradient R η P g w) w := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  simpa only [wrapped,wrappedGradient,map_add] using
    (carried_hasGradientAt R P H g hg w).hasFDerivAt.add (quadratic_hasGradientAt η w).hasFDerivAt

theorem gradient_formula (R η : ℝ) (P : E →L[ℝ] Z) (g : Z → Z) (w : E) :
    wrappedGradient R η P g w =
      scale R w • (P.adjoint (g (P (compress R w)))) +
        (η-scale R w^3/R^2*⟪w,P.adjoint (g (P (compress R w)))⟫) • w := by
  simp only [wrappedGradient,carriedGradient,compressDerivative_apply,sub_smul]
  abel

theorem adjoint_norm_bound {P : E →L[ℝ] Z} (hP : ‖P‖ ≤ 1) (v : Z) :
    ‖P.adjoint v‖ ≤ ‖v‖ := by
  have h := P.adjoint.le_opNorm v
  rw [LinearIsometryEquiv.norm_map] at h
  exact h.trans (by nlinarith [norm_nonneg v])

theorem carried_gradient_norm {R G : ℝ} (hR : 0 < R) (P : E →L[ℝ] Z)
    (hP : ‖P‖ ≤ 1) (g : Z → Z) (hG : ∀ z, ‖g z‖ ≤ G) (w : E) :
    ‖carriedGradient R P g w‖ ≤ G :=
  (compressDerivative_norm_le R hR w _).trans
    ((adjoint_norm_bound hP _).trans (hG _))

theorem carried_gradient_difference {R L G : ℝ} (hR : 0 < R)
    (hL : 0 ≤ L) (_hG : 0 ≤ G) (P : E →L[ℝ] Z) (hP : ‖P‖ ≤ 1)
    (g : Z → Z) (hgrad : ∀ z, ‖g z‖ ≤ G)
    (hlip : ∀ z v, ‖g z-g v‖ ≤ L*‖z-v‖) (w v : E) :
    ‖carriedGradient R P g w-carriedGradient R P g v‖ ≤
      (L+4*G/R)*‖w-v‖ := by
  let q := fun x => P.adjoint (g (P (compress R x)))
  have hq : ∀ x, ‖q x‖ ≤ G := fun x => (adjoint_norm_bound hP _).trans (hgrad _)
  have hqdiff : ‖q w-q v‖ ≤ L*‖w-v‖ := by
    have hc : ‖compress R w-compress R v‖ ≤ ‖w-v‖ := by
      simpa using (compress_lipschitz R hR).norm_sub_le w v
    have hp : ‖P (compress R w)-P (compress R v)‖ ≤ ‖w-v‖ := by
      rw [← map_sub]
      exact (P.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans
        (by simpa using hc))
    change ‖P.adjoint _-P.adjoint _‖ ≤ _
    rw [← map_sub]
    exact (adjoint_norm_bound hP _).trans ((hlip _ _).trans (mul_le_mul_of_nonneg_left hp hL))
  have he : carriedGradient R P g w-carriedGradient R P g v =
      compressDerivative R w (q w-q v)+
        (compressDerivative R w-compressDerivative R v) (q v) := by
    simp only [carriedGradient,map_sub,ContinuousLinearMap.sub_apply,q]
    abel
  rw [he]
  calc
    _ ≤ ‖compressDerivative R w (q w-q v)‖+
        ‖(compressDerivative R w-compressDerivative R v) (q v)‖ := norm_add_le _ _
    _ ≤ ‖q w-q v‖+(4/R)*‖w-v‖*‖q v‖ :=
      add_le_add (compressDerivative_norm_le R hR w _) (compressDerivative_difference_apply R hR w v _)
    _ ≤ L*‖w-v‖+(4/R)*‖w-v‖*G :=
      add_le_add hqdiff (mul_le_mul_of_nonneg_left (hq v) (by positivity))
    _ = _ := by ring

theorem wrapped_gradient_difference {R L G η : ℝ} (hR : 0 < R)
    (hL : 0 ≤ L) (hG : 0 ≤ G) (hη : 0 ≤ η) (P : E →L[ℝ] Z) (hP : ‖P‖ ≤ 1)
    (g : Z → Z) (hgrad : ∀ z, ‖g z‖ ≤ G)
    (hlip : ∀ z v, ‖g z-g v‖ ≤ L*‖z-v‖) (w v : E) :
    ‖wrappedGradient R η P g w-wrappedGradient R η P g v‖ ≤
      (L+4*G/R+η)*‖w-v‖ := by
  have he : wrappedGradient R η P g w-wrappedGradient R η P g v =
      (carriedGradient R P g w-carriedGradient R P g v)+η • (w-v) := by
    simp only [wrappedGradient,smul_sub]
    abel
  rw [he]
  have ht := norm_add_le (carriedGradient R P g w-carriedGradient R P g v) (η • (w-v))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hη] at ht
  exact ht.trans ((add_le_add_right
    (carried_gradient_difference hR hL hG P hP g hgrad hlip w v) _).trans_eq (by ring))

omit [CompleteSpace E] [CompleteSpace Z] in
theorem carried_contDiff (R : ℝ) (P : E →L[ℝ] Z) (H : Z → ℝ) (k : ℕ)
    (hH : ContDiff ℝ k H) : ContDiff ℝ k (carried R P H) :=
  hH.comp (P.contDiff.comp (compress_contDiff R k))

omit [CompleteSpace E] [CompleteSpace Z] in
theorem wrapped_contDiff (R η : ℝ) (P : E →L[ℝ] Z) (H : Z → ℝ) (k : ℕ)
    (hH : ContDiff ℝ k H) : ContDiff ℝ k (wrapped R η P H) :=
  (carried_contDiff R P H k hH).add (contDiff_const.mul (contDiff_norm_sq ℝ))

theorem carried_hessian_bound {R L G : ℝ} (hR : 0 < R)
    (hL : 0 ≤ L) (hG : 0 ≤ G) (P : E →L[ℝ] Z) (hP : ‖P‖ ≤ 1)
    (H : Z → ℝ) (g : Z → Z) (hg : ∀ z, HasGradientAt H (g z) z)
    (hgrad : ∀ z, ‖g z‖ ≤ G) (hlip : ∀ z v, ‖g z-g v‖ ≤ L*‖z-v‖) (w : E) :
    ‖fderiv ℝ (gradient (carried R P H)) w‖ ≤ L+4*G/R := by
  have he : gradient (carried R P H) = carriedGradient R P g :=
    funext fun w => (carried_hasGradientAt R P H g hg w).gradient
  rw [he]
  have hb : LipschitzWith ⟨L+4*G/R,by positivity⟩ (carriedGradient R P g) := by
    apply LipschitzWith.of_dist_le_mul
    intro w v
    simpa only [dist_eq_norm,NNReal.coe_mk] using
      carried_gradient_difference hR hL hG P hP g hgrad hlip w v
  exact norm_fderiv_le_of_lipschitz ℝ hb

theorem wrapped_hessian_bound {R L G η : ℝ} (hR : 0 < R)
    (hL : 0 ≤ L) (hG : 0 ≤ G) (hη : 0 ≤ η) (P : E →L[ℝ] Z) (hP : ‖P‖ ≤ 1)
    (H : Z → ℝ) (g : Z → Z) (hg : ∀ z, HasGradientAt H (g z) z)
    (hgrad : ∀ z, ‖g z‖ ≤ G) (hlip : ∀ z v, ‖g z-g v‖ ≤ L*‖z-v‖) (w : E) :
    ‖fderiv ℝ (gradient (wrapped R η P H)) w‖ ≤ L+4*G/R+η := by
  have he : gradient (wrapped R η P H) = wrappedGradient R η P g :=
    funext fun w => (wrapped_hasGradientAt R η P H g hg w).gradient
  rw [he]
  have hb : LipschitzWith ⟨L+4*G/R+η,by positivity⟩ (wrappedGradient R η P g) := by
    apply LipschitzWith.of_dist_le_mul
    intro w v
    simpa only [dist_eq_norm,NNReal.coe_mk] using
      wrapped_gradient_difference hR hL hG hη P hP g hgrad hlip w v
  exact norm_fderiv_le_of_lipschitz ℝ hb

omit [CompleteSpace Z] in
/-- Actual Hessian existence accompanies the bound for every C² input. -/
theorem wrapped_gradient_differentiable (R η : ℝ) (P : E →L[ℝ] Z) (H : Z → ℝ)
    (hH : ContDiff ℝ 2 H) : Differentiable ℝ (gradient (wrapped R η P H)) := by
  have hf := wrapped_contDiff R η P H 2 hH
  have hc : ContDiff ℝ 1 (gradient (wrapped R η P H)) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  exact hc.differentiable (by norm_num)

end Smoothness2601.RadialWrapper
