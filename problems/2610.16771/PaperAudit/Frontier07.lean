import Mathlib
import PaperAudit.Frontier06

open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000


section
-- Source component: CoerciveOperator.lean

namespace OriginalCoerciveOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem injective_of_coercive
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    Function.Injective A := by
  intro x y hxy
  have hzero : A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h := hcoercive (x - y)
  rw [hzero, inner_zero_left] at h
  have hs : ‖x - y‖ ^ 2 ≤ 0 := by
    apply (mul_le_mul_iff_right₀ hm).mp
    simpa only [mul_zero] using h
  have hn : ‖x - y‖ = 0 := by nlinarith only [hs, norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem bijective_of_coercive
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    Function.Bijective A := by
  have hi := injective_of_coercive A m hm hcoercive
  exact ⟨hi, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hi⟩

noncomputable def equivalenceOfCoercive
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr (bijective_of_coercive A m hm hcoercive).1)
    (LinearMap.range_eq_top.mpr (bijective_of_coercive A m hm hcoercive).2)

theorem equivalenceOfCoercive_apply
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) (v : E) :
    equivalenceOfCoercive A m hm hcoercive v = A v := rfl

theorem norm_vector_le_image_div
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) (v : E) :
    ‖v‖ ≤ ‖A v‖ / m := by
  have h1 := hcoercive v
  have h2 := real_inner_le_norm (A v) v
  apply (le_div_iff₀ hm).mpr
  by_cases hv : ‖v‖ = 0
  · rw [hv, zero_mul]
    exact norm_nonneg _
  · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    exact (mul_le_mul_iff_left₀ hp).mp (by nlinarith only [h1, h2])

theorem inverse_norm_le
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    ‖(equivalenceOfCoercive A m hm hcoercive).symm.toContinuousLinearMap‖ ≤ 1 / m := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity : 0 ≤ 1 / m)
  intro x
  have h := norm_vector_le_image_div A m hm hcoercive
    ((equivalenceOfCoercive A m hm hcoercive).symm x)
  have heq : A ((equivalenceOfCoercive A m hm hcoercive).symm x) = x :=
    (equivalenceOfCoercive A m hm hcoercive).apply_symm_apply x
  rw [heq] at h
  change ‖(equivalenceOfCoercive A m hm hcoercive).symm x‖ ≤ (1 / m) * ‖x‖
  calc
    _ ≤ ‖x‖ / m := h
    _ = (1 / m) * ‖x‖ := by ring

theorem inverse_resolvent_identity (A B : E ≃L[ℝ] E) :
    A.symm.toContinuousLinearMap - B.symm.toContinuousLinearMap =
      A.symm.toContinuousLinearMap.comp
        ((B.toContinuousLinearMap - A.toContinuousLinearMap).comp B.symm.toContinuousLinearMap) := by
  ext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, map_sub, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

theorem inverse_difference_norm
    (A B : E ≃L[ℝ] E) :
    ‖A.symm.toContinuousLinearMap - B.symm.toContinuousLinearMap‖ ≤
      ‖A.symm.toContinuousLinearMap‖ * ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ *
        ‖B.symm.toContinuousLinearMap‖ := by
  rw [inverse_resolvent_identity]
  let P := A.symm.toContinuousLinearMap
  let R := B.toContinuousLinearMap - A.toContinuousLinearMap
  let S := B.symm.toContinuousLinearMap
  change ‖P.comp (R.comp S)‖ ≤ ‖P‖ * ‖R‖ * ‖S‖
  calc
    ‖P.comp (R.comp S)‖ ≤ ‖P‖ * ‖R.comp S‖ := ContinuousLinearMap.opNorm_comp_le P (R.comp S)
    _ ≤ ‖P‖ * (‖R‖ * ‖S‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le R S) (norm_nonneg P)
    _ = ‖P‖ * ‖R‖ * ‖S‖ := (mul_assoc _ _ _).symm

theorem derivative_coercive_of_strong_monotonicity
    (T : E → E) (m : ℝ)
    (hstrong : ∀ x y : E, m * ‖x - y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y))
    (z : E) (D : E →L[ℝ] E) (hD : HasFDerivAt T D z) (v : E) :
    m * ‖v‖ ^ 2 ≤ inner ℝ (D v) v := by
  let φ : ℝ → ℝ := fun t => inner ℝ (T (z + t • v)) v - (m * ‖v‖ ^ 2) * t
  have hmono : Monotone φ := by
    intro s t hst
    by_cases heq : s = t
    · rw [heq]
    · have hd : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hst heq)
      have hdif : (z + t • v) - (z + s • v) = (t - s) • v := by module
      have hh := hstrong (z + t • v) (z + s • v)
      rw [hdif, norm_smul, Real.norm_eq_abs, abs_of_pos hd,
        mul_pow, inner_smul_right] at hh
      have hfactor : (t - s) * (m * (t - s) * ‖v‖ ^ 2) ≤
          (t - s) * inner ℝ (T (z + t • v) - T (z + s • v)) v := by
        nlinarith only [hh]
      have hc := (mul_le_mul_iff_right₀ hd).mp hfactor
      rw [inner_sub_left] at hc
      dsimp only [φ]
      nlinarith only [hc]
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) z).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;>
      first | rfl | simp only [zero_add, one_smul, Pi.add_apply, id_eq]
  have hcomp : HasDerivAt (fun t : ℝ => T (z + t • v)) (D v) 0 := by
    exact hD.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hscalar : HasDerivAt φ (inner ℝ (D v) v - m * ‖v‖ ^ 2) 0 := by
    convert (hcomp.inner ℝ (hasDerivAt_const (0 : ℝ) v)).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul (m * ‖v‖ ^ 2)) using 1 <;>
      first | rfl | simp only [inner_zero_right, add_zero, zero_add, mul_one]
  have hp := hscalar.nonneg_of_monotone hmono
  linarith only [hp]

end OriginalCoerciveOperator
end

section
-- Source component: SaddleImplicitRegularity.lean

namespace OriginalSaddleImplicit

open Filter
open scoped Topology

variable {X W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Actual continuous zero selections agree locally with the implicit branch.
This helper does not assert invertibility from convexity: that is a separate obligation. -/
theorem actual_selection_contDiffAt
    (R : X × W → W) (s : X → W) (x : X)
    (hC1 : ContDiffAt ℝ 1 R (x, s x))
    (hinv : (fderiv ℝ R (x, s x) ∘L ContinuousLinearMap.inr ℝ X W).IsInvertible)
    (hs : ContinuousAt s x) (hzero : ∀ t : X, R (t, s t) = 0) :
    ContDiffAt ℝ 1 s x := by
  let ψ := hC1.implicitFunction (by norm_num) hinv
  have hevent := hC1.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv
  have hp : Tendsto (fun t : X => (t, s t)) (𝓝 x) (𝓝 (x, s x)) :=
    continuousAt_id.prodMk hs
  have heq : s =ᶠ[𝓝 x] ψ := by
    filter_upwards [hp.eventually hevent] with t ht
    exact (ht.mp (by rw [hzero t, hzero x])).symm
  exact (hC1.contDiffAt_implicitFunction (by norm_num) hinv).congr_of_eventuallyEq heq

variable {Z : Type*}
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]

/-- C2 of the scalar objective supplies C1 of its actual Riesz gradient. -/
theorem contDiff_gradient_of_contDiff2 (J : Z → ℝ) (hC2 : ContDiff ℝ 2 J) :
    ContDiff ℝ 1 (gradient J) := by
  have hder : ContDiff ℝ 1 (fderiv ℝ J) := hC2.fderiv_right (by norm_num)
  have heq : gradient J = fun z => (InnerProductSpace.toDual ℝ Z).symm (fderiv ℝ J z) := by
    funext z
    rfl
  rw [heq]
  exact (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.contDiff.comp hder


section Saddle
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev Joint (E F : Type*) := WithLp 2 (E × F)

noncomputable def reflection : Joint E F →L[ℝ] Joint E F :=
  (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.comp
      (WithLp.fstL 2 ℝ E F) -
    (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap.comp
      (WithLp.sndL 2 ℝ E F)

theorem reflection_fst (w : Joint E F) : (reflection w).fst = w.fst := by
  simp [reflection, JointSliceRegularity.axisX, JointSliceRegularity.axisY]

theorem reflection_snd (w : Joint E F) : (reflection w).snd = -w.snd := by
  simp [reflection, JointSliceRegularity.axisX, JointSliceRegularity.axisY]

noncomputable def signedSaddleMap (J : Joint E F → ℝ) (L : ℝ) (w : Joint E F) :
    Joint E F :=
  reflection (gradient J w) + (2 * L) • JointSliceRegularity.axisX w.fst

noncomputable def residual (J : Joint E F → ℝ) (L : ℝ) (p : E × Joint E F) :
    Joint E F :=
  signedSaddleMap J L p.2 - (2 * L) • JointSliceRegularity.axisX p.1

theorem signedSaddleMap_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J) :
    ContDiff ℝ 1 (signedSaddleMap J L) := by
  unfold signedSaddleMap
  have h1 : ContDiff ℝ 1 (fun w : Joint E F => reflection (gradient J w)) :=
    (reflection (E := E) (F := F)).contDiff.comp (contDiff_gradient_of_contDiff2 J hC2)
  have h2 : ContDiff ℝ 1 (fun w : Joint E F => JointSliceRegularity.axisX w.fst) :=
    (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.contDiff.comp
      (WithLp.fstL 2 ℝ E F).contDiff
  exact h1.add (h2.const_smul (2 * L))

theorem residual_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J) :
    ContDiff ℝ 1 (residual J L) := by
  unfold residual
  exact ((signedSaddleMap_contDiff J L hC2).comp contDiff_snd).sub
    (((JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.contDiff.comp
      contDiff_fst).const_smul (2 * L))

/-- The signed saddle operator is strongly monotone in the full L2 product.
The mixed terms cancel using four supports, without a symmetry premise on a supplied Hessian. -/
theorem slice_gradient_four_supports
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (u u' : E) (v v' : F) :
    -L * ‖u - u'‖ ^ 2 + μ * ‖v - v'‖ ^ 2 ≤
      inner ℝ (gradient (fun t => f t v) u - gradient (fun t => f t v') u') (u - u') -
      inner ℝ (gradient (f u) v - gradient (f u') v') (v - v') := by
  have hx := OriginalSaddleRegularity.smooth_gradient_lower_support
    (fun t => f t v) L hL (hdiffX v) (hxx v) u u'
  have hx' := OriginalSaddleRegularity.smooth_gradient_lower_support
    (fun t => f t v') L hL (hdiffX v') (hxx v') u' u
  have hy := PacketCore.strongConvex_support (fun y => -f u y) μ
    (hsc u) (hdiffY u).neg v v'
  have hy' := PacketCore.strongConvex_support (fun y => -f u' y) μ
    (hsc u') (hdiffY u').neg v' v
  rw [OriginalSaddleRegularity.gradient_neg_of_differentiable (f u) (hdiffY u),
    inner_neg_left] at hy
  rw [OriginalSaddleRegularity.gradient_neg_of_differentiable (f u') (hdiffY u'),
    inner_neg_left] at hy'
  rw [show u' - u = -(u - u') by abel, norm_neg, inner_neg_right] at hx
  rw [show v' - v = -(v - v') by abel, norm_neg, inner_neg_right] at hy
  simp only [inner_sub_left]
  nlinarith only [hx, hx', hy, hy']


theorem signedSaddleMap_energy
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L)
    (hJ : Differentiable ℝ J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (w w' : Joint E F) :
    L * ‖w.fst - w'.fst‖ ^ 2 + μ * ‖w.snd - w'.snd‖ ^ 2 ≤
      inner ℝ (signedSaddleMap J L w - signedSaddleMap J L w') (w - w') := by
  have he := slice_gradient_four_supports (JointSliceRegularity.curry J) L μ hL
    (JointSliceRegularity.differentiable_x_slice J hJ)
    (JointSliceRegularity.differentiable_y_slice J hJ) hsc
    (fun y x z => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip x z y)
    w.fst w'.fst w.snd w'.snd
  rw [JointSliceRegularity.gradient_x_slice_eq_projection J hJ,
    JointSliceRegularity.gradient_x_slice_eq_projection J hJ,
    JointSliceRegularity.gradient_y_slice_eq_projection J hJ,
    JointSliceRegularity.gradient_y_slice_eq_projection J hJ,
    JointSliceRegularity.point_eq_toLp, JointSliceRegularity.point_eq_toLp] at he
  have hw : WithLp.toLp 2 (w.fst, w.snd) = w := by rfl
  have hw' : WithLp.toLp 2 (w'.fst, w'.snd) = w' := by rfl
  rw [hw, hw'] at he
  have hi : inner ℝ (signedSaddleMap J L w - signedSaddleMap J L w') (w - w') =
      inner ℝ ((gradient J w).fst - (gradient J w').fst) (w.fst - w'.fst) -
        inner ℝ ((gradient J w).snd - (gradient J w').snd) (w.snd - w'.snd) +
          2 * L * ‖w.fst - w'.fst‖ ^ 2 := by
    rw [WithLp.prod_inner_apply]
    change inner ℝ (signedSaddleMap J L w - signedSaddleMap J L w').fst (w - w').fst +
      inner ℝ (signedSaddleMap J L w - signedSaddleMap J L w').snd (w - w').snd = _
    simp only [signedSaddleMap, WithLp.sub_fst, WithLp.sub_snd, WithLp.add_fst,
      WithLp.add_snd, WithLp.smul_fst, WithLp.smul_snd, reflection_fst, reflection_snd]
    change inner ℝ ((gradient J w).fst + (2 * L) • w.fst -
        ((gradient J w').fst + (2 * L) • w'.fst)) (w.fst - w'.fst) +
      inner ℝ (-(gradient J w).snd + (2 * L) • (0 : F) -
        (-(gradient J w').snd + (2 * L) • (0 : F))) (w.snd - w'.snd) = _
    simp only [smul_zero, add_zero]
    rw [show (gradient J w).fst + (2 * L) • w.fst -
      ((gradient J w').fst + (2 * L) • w'.fst) =
      ((gradient J w).fst - (gradient J w').fst) +
        (2 * L) • (w.fst - w'.fst) by module]
    rw [show -(gradient J w).snd - -(gradient J w').snd =
      -((gradient J w).snd - (gradient J w').snd) by abel]
    simp only [inner_add_left, real_inner_smul_left, inner_neg_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [hi]
  linarith

theorem signedSaddleMap_strong_monotone
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L)
    (hJ : Differentiable ℝ J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (w w' : Joint E F) :
    min L μ * ‖w - w'‖ ^ 2 ≤
      inner ℝ (signedSaddleMap J L w - signedSaddleMap J L w') (w - w') := by
  have he := signedSaddleMap_energy J L μ hL hJ hsc hLip w w'
  have hn := WithLp.prod_norm_sq_eq_of_L2 (w - w')
  change ‖w - w'‖ ^ 2 = ‖w.fst - w'.fst‖ ^ 2 + ‖w.snd - w'.snd‖ ^ 2 at hn
  have h1 := mul_le_mul_of_nonneg_right (min_le_left L μ) (sq_nonneg ‖w.fst - w'.fst‖)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right L μ) (sq_nonneg ‖w.snd - w'.snd‖)
  rw [hn, mul_add]
  exact (add_le_add h1 h2).trans he

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem residual_zero_at_actual_saddle
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hJ : Differentiable ℝ J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : residual J L (x,
      OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L x) = 0 := by
  let f := JointSliceRegularity.curry J
  let u := OriginalSaddleTransfer.uStar f L x
  let v := OriginalSaddleTransfer.vStar f L x
  let z := OriginalSaddleStability.zStar f L x
  have hdiffX := JointSliceRegularity.differentiable_x_slice J hJ
  have hdiffY := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y x t => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip x t y
  have hxy := fun x y t => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip x y t
  obtain ⟨hphi, hweak⟩ := OriginalSaddleTransfer.phi_regular_from_slices
    f L μ hL hμ hdiffX hdiffY hsc hxx hxy
  have hFOC := MoreauTransfer.prox_first_order (OriginalSaddleTransfer.phi f) L
    hL hphi hweak x
  have hPhiGrad := (OriginalSaddleTransfer.phi_hasGradientAt_yStar f L μ hL hμ
    hdiffX hdiffY hsc hxx hxy u).gradient
  change gradient (OriginalSaddleTransfer.phi f) u = gradient (fun t => f t v) u at hPhiGrad
  have hx : gradient (fun t => f t v) u = (2 * L) • (x - u) :=
    hPhiGrad.symm.trans hFOC
  have hy : gradient (f u) v = 0 := by
    have hneg : gradient (fun y => -f u y) v = 0 :=
      PacketCore.gradient_eq_zero_at_global_min _ _
        (fun y => neg_le_neg (OriginalSaddleTransfer.yStar_maximizes
          f μ hμ hsc hdiffY u y))
    rw [OriginalSaddleRegularity.gradient_neg_of_differentiable (f u) (hdiffY u)] at hneg
    exact neg_eq_zero.mp hneg
  have hz : JointSliceRegularity.point u v = z := JointSliceRegularity.point_eq_toLp u v
  have hgx : (gradient J z).fst = (2 * L) • (x - u) := by
    rw [← hz, ← JointSliceRegularity.gradient_x_slice_eq_projection J hJ]
    exact hx
  have hgy : (gradient J z).snd = 0 := by
    rw [← hz, ← JointSliceRegularity.gradient_y_slice_eq_projection J hJ]
    exact hy
  change residual J L (x, z) = 0
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · change (residual J L (x, z)).fst = 0
    simp only [residual, signedSaddleMap, WithLp.sub_fst, WithLp.add_fst,
      WithLp.smul_fst, reflection_fst]
    change (gradient J z).fst + (2 * L) • u - (2 * L) • x = 0
    rw [hgx]
    module
  · change (residual J L (x, z)).snd = 0
    simp only [residual, signedSaddleMap, WithLp.sub_snd, WithLp.add_snd,
      WithLp.smul_snd, reflection_snd]
    change -(gradient J z).snd + (2 * L) • (0 : F) - (2 * L) • (0 : F) = 0
    simp only [hgy, neg_zero, smul_zero, add_zero, sub_zero]


theorem residual_partial_fderiv
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J)
    (x : E) (w : Joint E F) :
    fderiv ℝ (residual J L) (x, w) ∘L ContinuousLinearMap.inr ℝ E (Joint E F) =
      fderiv ℝ (signedSaddleMap J L) w := by
  have hR := ((residual_contDiff J L hC2).differentiable (by norm_num) (x, w)).hasFDerivAt
  have hpair : HasFDerivAt (fun t : Joint E F => (x, t))
      (ContinuousLinearMap.inr ℝ E (Joint E F)) w := by
    convert! (hasFDerivAt_const (c := x) w).prodMk (hasFDerivAt_id w) using 1 <;> rfl
  have hcomp := hR.comp w hpair
  have hB := ((signedSaddleMap_contDiff J L hC2).differentiable (by norm_num) w).hasFDerivAt
  have hfixed : HasFDerivAt (fun t => residual J L (x, t))
      (fderiv ℝ (signedSaddleMap J L) w) w := by
    simpa only [residual] using hB.sub_const ((2 * L) • JointSliceRegularity.axisX x)
  exact hcomp.unique hfixed

theorem residual_partial_isInvertible
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (w : Joint E F) :
    (fderiv ℝ (residual J L) (x, w) ∘L ContinuousLinearMap.inr ℝ E (Joint E F)).IsInvertible := by
  rw [residual_partial_fderiv J L hC2]
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hD := ((signedSaddleMap_contDiff J L hC2).differentiable (by norm_num) w).hasFDerivAt
  have hc := OriginalCoerciveOperator.derivative_coercive_of_strong_monotonicity
    (signedSaddleMap J L) (min L μ)
    (signedSaddleMap_strong_monotone J L μ hL hJ hsc hLip) w _ hD
  exact ⟨OriginalCoerciveOperator.equivalenceOfCoercive _ (min L μ)
    (lt_min hL hμ) hc, rfl⟩

theorem actual_saddle_contDiff_from_joint
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖) :
    ContDiff ℝ 1 (OriginalSaddleTransfer.uStar (JointSliceRegularity.curry J) L) ∧
    ContDiff ℝ 1 (OriginalSaddleTransfer.vStar (JointSliceRegularity.curry J) L) ∧
    ContDiff ℝ 1 (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdiffX := JointSliceRegularity.differentiable_x_slice J hJ
  have hdiffY := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y x t => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip x t y
  have hxy := fun x y t => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip x y t
  have hzl : LipschitzWith ⟨2 * Real.sqrt (1 + L / μ), by positivity⟩
      (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) := by
    apply LipschitzWith.of_dist_le_mul
    intro x x'
    change dist _ _ ≤ (2 * Real.sqrt (1 + L / μ)) * dist x x'
    simpa only [dist_eq_norm] using
      OriginalSaddleStability.actual_saddle_lipschitz_joint (JointSliceRegularity.curry J)
        L μ hL hμ hdiffX hdiffY hsc hxx hxy x x'
  have hz : ContDiff ℝ 1 (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact actual_selection_contDiffAt (residual J L) _ x
      (residual_contDiff J L hC2).contDiffAt
      (residual_partial_isInvertible J L μ hL hμ hC2 hsc hLip x _)
      hzl.continuous.continuousAt
      (residual_zero_at_actual_saddle J L μ hL hμ hJ hsc hLip)
  refine ⟨?_, ?_, hz⟩
  · convert! (WithLp.fstL 2 ℝ E F).contDiff.comp hz using 1 <;> rfl
  · convert! (WithLp.sndL 2 ℝ E F).contDiff.comp hz using 1 <;> rfl


theorem square_root_sensitivity_from_standing_joint
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hconcave : ∀ x : E, StrongConcaveOn (Set.univ : Set F) μ
      (fun y => J (WithLp.toLp 2 (x, y))))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖) :
    let f := JointSliceRegularity.curry J
    ContDiff ℝ 1 (OriginalSaddleStability.zStar f L) ∧
    (∀ x : E, ∀ h : E,
      ‖(fderiv ℝ (OriginalSaddleStability.zStar f L) x h).fst‖ ≤ 2 * ‖h‖ ∧
      ‖(fderiv ℝ (OriginalSaddleStability.zStar f L) x h).snd‖ ≤
        2 * Real.sqrt (L / μ) * ‖h‖ ∧
      ‖fderiv ℝ (OriginalSaddleStability.zStar f L) x h‖ ≤
        2 * Real.sqrt (1 + L / μ) * ‖h‖) ∧
    (∀ x x' : E,
      ‖OriginalSaddleTransfer.vStar f L x - OriginalSaddleTransfer.vStar f L x'‖ ≤
        2 * Real.sqrt (L / μ) * ‖x - x'‖) := by
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hconcave' : ∀ x : E, StrongConcaveOn (Set.univ : Set F) μ (f x) := by
    intro x
    have heq : f x = (fun y : F => J (WithLp.toLp 2 (x, y))) := by
      funext y
      exact congrArg J (JointSliceRegularity.point_eq_toLp x y)
    rw [heq]
    exact hconcave x
  have hsc := JointSliceRegularity.strongConvex_negative_y_slice J μ hconcave'
  have hdiffX := JointSliceRegularity.differentiable_x_slice J hJ
  have hdiffY := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y x t => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip x t y
  have hxy := fun x y t => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip x y t
  obtain ⟨hu, hv, hz⟩ := actual_saddle_contDiff_from_joint J L μ hL hμ hC2 hsc hLip
  refine ⟨hz, ?_, ?_⟩
  · intro x h
    let Z := fderiv ℝ (OriginalSaddleStability.zStar f L) x
    have hZ : HasFDerivAt (OriginalSaddleStability.zStar f L) Z x :=
      (hz.differentiable (by norm_num) x).hasFDerivAt
    have hU : HasFDerivAt (OriginalSaddleTransfer.uStar f L)
        ((WithLp.fstL 2 ℝ E F).comp Z) x := by
      convert! (WithLp.fstL 2 ℝ E F).hasFDerivAt.comp x hZ using 1 <;> rfl
    have hV : HasFDerivAt (OriginalSaddleTransfer.vStar f L)
        ((WithLp.sndL 2 ℝ E F).comp Z) x := by
      convert! (WithLp.sndL 2 ℝ E F).hasFDerivAt.comp x hZ using 1 <;> rfl
    exact OriginalSaddleStability.derivative_bounds_from_checked_differentials f L μ hL hμ
      hdiffX hdiffY hsc hxx hxy x _ _ Z hU hV hZ h
  · intro x x'
    exact (OriginalSaddleStability.actual_saddle_lipschitz_components f L μ hL hμ
      hdiffX hdiffY hsc hxx hxy x x').2

end Saddle

end OriginalSaddleImplicit
end

section
-- Source component: SaddleTangentRegularity.lean

namespace OriginalSaddleTangent

open OriginalSaddleImplicit

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def primalProjection : Joint E F →L[ℝ] Joint E F :=
  (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.comp
    (WithLp.fstL 2 ℝ E F)

noncomputable def saddleHessian (J : Joint E F → ℝ) (L : ℝ) (w : Joint E F) :
    Joint E F →L[ℝ] Joint E F :=
  fderiv ℝ (gradient J) w + (2 * L) • primalProjection

noncomputable def centerDerivative (L : ℝ) : E →L[ℝ] Joint E F :=
  (2 * L) • (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap

theorem reflection_axisX (x : E) :
    reflection (JointSliceRegularity.axisX (F := F) x) =
      JointSliceRegularity.axisX (F := F) x := by
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · exact reflection_fst _
  · change (reflection (JointSliceRegularity.axisX (F := F) x)).snd = 0
    rw [reflection_snd]
    change -(0 : F) = 0
    exact neg_zero

theorem reflection_involution (w : Joint E F) : reflection (reflection w) = w := by
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · exact (reflection_fst _).trans (reflection_fst _)
  · change (reflection (reflection w)).snd = w.snd
    rw [reflection_snd, reflection_snd, neg_neg]

noncomputable def reflectionEquiv : Joint E F ≃L[ℝ] Joint E F :=
  ContinuousLinearEquiv.equivOfInverse reflection reflection reflection_involution reflection_involution

theorem signed_map_as_reflection (J : Joint E F → ℝ) (L : ℝ) (w : Joint E F) :
    signedSaddleMap J L w = reflection (gradient J w + (2 * L) • JointSliceRegularity.axisX w.fst) := by
  simp only [map_add, map_smul, reflection_axisX, signedSaddleMap]

theorem signed_map_hasFDerivAt
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J) (w : Joint E F) :
    HasFDerivAt (signedSaddleMap J L) (reflection.comp (saddleHessian J L w)) w := by
  have hgrad := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num) w).hasFDerivAt
  have hproj : HasFDerivAt (fun t : Joint E F => JointSliceRegularity.axisX t.fst)
      (primalProjection (E := E) (F := F)) w := by
    exact primalProjection.hasFDerivAt
  have hraw : HasFDerivAt (fun t : Joint E F => gradient J t +
      (2 * L) • JointSliceRegularity.axisX t.fst) (saddleHessian J L w) w :=
    hgrad.add (hproj.const_smul (2 * L))
  have hc := reflection.hasFDerivAt.comp w hraw
  convert! hc using 1 <;> first | rfl | (funext t; exact signed_map_as_reflection J L t)

theorem gradient_derivative_selfadjoint
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (J : Z → ℝ) (hC2 : ContDiff ℝ 2 J) (w : Z) :
    (fderiv ℝ (gradient J) w).adjoint = fderiv ℝ (gradient J) w := by
  have hfd := ((hC2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) w).hasFDerivAt
  have hgrad : HasFDerivAt (gradient J)
      ((InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ J) w)) w := by
    convert! (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp
      w hfd using 1 <;> rfl
  have hs : IsSymmSndFDerivAt ℝ J w := hC2.contDiffAt.isSymmSndFDerivAt (by simp)
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro a b
  rw [hgrad.fderiv]
  change inner ℝ ((InnerProductSpace.toDual ℝ Z).symm
      (fderiv ℝ (fderiv ℝ J) w a)) b =
    inner ℝ a ((InnerProductSpace.toDual ℝ Z).symm (fderiv ℝ (fderiv ℝ J) w b))
  calc
    inner ℝ ((InnerProductSpace.toDual ℝ Z).symm
        (fderiv ℝ (fderiv ℝ J) w a)) b = fderiv ℝ (fderiv ℝ J) w a b :=
      InnerProductSpace.toDual_symm_apply
    _ = fderiv ℝ (fderiv ℝ J) w b a := hs a b
    _ = inner ℝ ((InnerProductSpace.toDual ℝ Z).symm
        (fderiv ℝ (fderiv ℝ J) w b)) a := InnerProductSpace.toDual_symm_apply.symm
    _ = inner ℝ a ((InnerProductSpace.toDual ℝ Z).symm
        (fderiv ℝ (fderiv ℝ J) w b)) := real_inner_comm _ _

theorem primalProjection_selfadjoint :
    (primalProjection (E := E) (F := F)).adjoint = primalProjection := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro a b
  change inner ℝ (JointSliceRegularity.axisX a.fst) b =
    inner ℝ a (JointSliceRegularity.axisX b.fst)
  calc
    inner ℝ (JointSliceRegularity.axisX a.fst) b =
        inner ℝ b (JointSliceRegularity.axisX a.fst) := real_inner_comm _ _
    _ = inner ℝ b.fst a.fst := JointSliceRegularity.inner_axisX b a.fst
    _ = inner ℝ a.fst b.fst := real_inner_comm _ _
    _ = inner ℝ a (JointSliceRegularity.axisX b.fst) :=
      (JointSliceRegularity.inner_axisX a b.fst).symm

theorem saddleHessian_selfadjoint
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J) (w : Joint E F) :
    (saddleHessian J L w).adjoint = saddleHessian J L w := by
  simp only [saddleHessian, map_add, map_smul,
    gradient_derivative_selfadjoint J hC2 w, primalProjection_selfadjoint]

theorem centerDerivative_adjoint (L : ℝ) :
    (centerDerivative (E := E) (F := F) L).adjoint = (2 * L) • WithLp.fstL 2 ℝ E F := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro w h
  change inner ℝ ((2 * L) • w.fst) h =
    inner ℝ w ((2 * L) • JointSliceRegularity.axisX h)
  rw [real_inner_smul_left, real_inner_smul_right, JointSliceRegularity.inner_axisX]

theorem saddleHessian_difference
    (J : Joint E F → ℝ) (L : ℝ) (w w' : Joint E F) :
    saddleHessian J L w - saddleHessian J L w' =
      fderiv ℝ (gradient J) w - fderiv ℝ (gradient J) w' := by
  unfold saddleHessian
  abel

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem actual_saddle_tangent
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) :
    (saddleHessian J L (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L x)).comp
      (fderiv ℝ (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) x) =
      centerDerivative L := by
  let z := OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hz := (actual_saddle_contDiff_from_joint J L μ hL hμ hC2 hsc hLip).2.2
  have hroot : (fun t : E => signedSaddleMap J L (z t)) = centerDerivative L := by
    funext t
    exact sub_eq_zero.mp (residual_zero_at_actual_saddle J L μ hL hμ hJ hsc hLip t)
  have hcomp := (signed_map_hasFDerivAt J L hC2 (z x)).comp x
    ((hz.differentiable (by norm_num) x).hasFDerivAt)
  change HasFDerivAt (fun t => signedSaddleMap J L (z t)) _ x at hcomp
  rw [hroot] at hcomp
  have heq := hcomp.unique (centerDerivative (E := E) (F := F) L).hasFDerivAt
  ext h
  have hh := congrArg (reflection (E := E) (F := F)) (DFunLike.congr_fun heq h)
  simp only [ContinuousLinearMap.comp_apply, reflection_involution, centerDerivative,
    ContinuousLinearMap.smul_apply, map_smul] at hh
  change (saddleHessian J L (z x))
    (fderiv ℝ (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) x h) =
      (2 * L) • reflection (JointSliceRegularity.axisX h) at hh
  rw [reflection_axisX] at hh
  exact hh

theorem saddleHessian_isInvertible
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (w : Joint E F) : (saddleHessian J L w).IsInvertible := by
  have hD : (fderiv ℝ (signedSaddleMap J L) w).IsInvertible := by
    rw [← residual_partial_fderiv J L hC2 (0 : E)]
    exact residual_partial_isInvertible J L μ hL hμ hC2 hsc hLip 0 w
  rw [(signed_map_hasFDerivAt J L hC2 w).fderiv] at hD
  have heq : saddleHessian J L w = reflection.comp (reflection.comp (saddleHessian J L w)) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, reflection_involution]
  rw [heq]
  exact ((ContinuousLinearMap.isInvertible_equiv (f := reflectionEquiv)).comp hD)

theorem actual_saddle_derivative_formula
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) :
    fderiv ℝ (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) x =
      (saddleHessian J L (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L x)).inverse.comp
        (centerDerivative L) := by
  have ht := actual_saddle_tangent J L μ hL hμ hC2 hsc hLip x
  have hi := saddleHessian_isInvertible J L μ hL hμ hC2 hsc hLip
    (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L x)
  ext h
  have hh := congrArg ((saddleHessian J L
    (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L x)).inverse)
    (DFunLike.congr_fun ht h)
  simpa only [ContinuousLinearMap.comp_apply, hi.inverse_apply_self] using hh

end OriginalSaddleTangent
end

section
-- Source component: PrimalElimination.lean

namespace OriginalPrimalElimination

open OriginalSaddleImplicit

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E]

noncomputable def primal (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) : E :=
  MoreauTransfer.prox (fun u => JointSliceRegularity.curry J u y) L x

noncomputable def blockUU (J : Joint E F → ℝ) (w : Joint E F) : E →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E F).comp
    ((fderiv ℝ (gradient J) w).comp (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap)

noncomputable def blockUY (J : Joint E F → ℝ) (w : Joint E F) : F →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E F).comp
    ((fderiv ℝ (gradient J) w).comp (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap)

noncomputable def primalHessian (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) : E →L[ℝ] E :=
  blockUU J (JointSliceRegularity.point (primal J L x y) y) +
    (2 * L) • ContinuousLinearMap.id ℝ E

noncomputable def residual (J : Joint E F → ℝ) (L : ℝ) (x : E) (p : F × E) : E :=
  (gradient J (JointSliceRegularity.point p.2 p.1)).fst + (2 * L) • (p.2 - x)

theorem slice_weak_convex
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖) (y : F) :
    ConvexOn ℝ (Set.univ : Set E)
      (fun u => JointSliceRegularity.curry J u y + L / 2 * ‖u‖ ^ 2) := by
  have hs := OriginalSaddleRegularity.smooth_function_weakly_convex
    (fun u => JointSliceRegularity.curry J u y) L hL
    (JointSliceRegularity.differentiable_x_slice J hJ y)
    (fun u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y)
  have hc := strongConvexOn_iff_convex.mp hs
  convert hc using 1 <;> (first | rfl | (funext u; ring))

theorem primal_is_unique_minimizer
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    (∀ u : E, JointSliceRegularity.curry J (primal J L x y) y +
      L * ‖primal J L x y - x‖ ^ 2 ≤ JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2) ∧
    (∀ u : E, (∀ v : E, JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2 ≤
      JointSliceRegularity.curry J v y + L * ‖v - x‖ ^ 2) → u = primal J L x y) := by
  have hd := JointSliceRegularity.differentiable_x_slice J hJ y
  have hw := slice_weak_convex J L hL hJ hLip y
  exact ⟨MoreauTransfer.prox_minimizes _ L hL hd hw x,
    fun u hu => MoreauTransfer.prox_is_unique _ L hL hd hw x u hu⟩

theorem primal_first_order
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    gradient (fun u => JointSliceRegularity.curry J u y) (primal J L x y) =
      (2 * L) • (x - primal J L x y) := by
  exact MoreauTransfer.prox_first_order _ L hL
    (JointSliceRegularity.differentiable_x_slice J hJ y)
    (slice_weak_convex J L hL hJ hLip y) x

theorem primal_lipschitz
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖primal J L x y - primal J L x y'‖ ≤ ‖y - y'‖ := by
  let u := primal J L x y
  let u' := primal J L x y'
  let f := JointSliceRegularity.curry J
  have hs := OriginalSaddleRegularity.smooth_function_weakly_convex
    (fun t => f t y) L hL (JointSliceRegularity.differentiable_x_slice J hJ y)
    (fun t s => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip t s y)
  have he := PacketCore.gradient_strong_monotone (fun t => f t y) (-L) hs
    (JointSliceRegularity.differentiable_x_slice J hJ y) u u'
  have hu := primal_first_order J L hL hJ hLip x y
  have hu' := primal_first_order J L hL hJ hLip x y'
  change gradient (fun t => f t y) u = (2 * L) • (x - u) at hu
  change gradient (fun t => f t y') u' = (2 * L) • (x - u') at hu'
  have hsplit : gradient (fun t => f t y) u - gradient (fun t => f t y) u' =
      -(2 * L) • (u - u') +
        (gradient (fun t => f t y') u' - gradient (fun t => f t y) u') := by
    rw [hu, hu']
    module
  rw [hsplit, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at he
  have hi := real_inner_le_norm
    (gradient (fun t => f t y') u' - gradient (fun t => f t y) u') (u - u')
  have hcross := JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u' y' y
  rw [norm_sub_rev y' y] at hcross
  have hm := mul_le_mul_of_nonneg_right hcross (norm_nonneg (u - u'))
  change ‖u - u'‖ ≤ ‖y - y'‖
  by_cases hz : ‖u - u'‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hp : 0 < ‖u - u'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hmain : L * ‖u - u'‖ * ‖u - u'‖ ≤ L * ‖y - y'‖ * ‖u - u'‖ := by
      nlinarith only [he, hi, hm]
    have hc := (mul_le_mul_iff_left₀ hp).mp hmain
    exact (mul_le_mul_iff_right₀ hL).mp hc

theorem primal_graph_lipschitz
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖JointSliceRegularity.point (primal J L x y) y -
      JointSliceRegularity.point (primal J L x y') y'‖ ≤ Real.sqrt 2 * ‖y - y'‖ := by
  have hu := primal_lipschitz J L hL hJ hLip x y y'
  have hu2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hu
  have hn := WithLp.prod_norm_sq_eq_of_L2
    (JointSliceRegularity.point (primal J L x y) y -
      JointSliceRegularity.point (primal J L x y') y')
  rw [JointSliceRegularity.point_eq_toLp, JointSliceRegularity.point_eq_toLp] at hn
  change ‖WithLp.toLp 2 (primal J L x y, y) - WithLp.toLp 2 (primal J L x y', y')‖ ^ 2 =
    ‖primal J L x y - primal J L x y'‖ ^ 2 + ‖y - y'‖ ^ 2 at hn
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt 2 * ‖y - y'‖)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [JointSliceRegularity.point_eq_toLp, JointSliceRegularity.point_eq_toLp]
  nlinarith only [hn, hu2]


theorem gradient_x_hasFDerivAt_x
    (J : Joint E F → ℝ) (hC2 : ContDiff ℝ 2 J) (u : E) (y : F) :
    HasFDerivAt (fun z : E => gradient (fun t => JointSliceRegularity.curry J t y) z)
      (blockUU J (JointSliceRegularity.point u y)) u := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hgrad := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
    (JointSliceRegularity.point u y)).hasFDerivAt
  have hc := (WithLp.fstL 2 ℝ E F).hasFDerivAt.comp u
    (hgrad.comp u (JointSliceRegularity.point_hasFDerivAt_x u y))
  have heq : (fun z : E => gradient (fun t => JointSliceRegularity.curry J t y) z) =
      (fun z => (gradient J (JointSliceRegularity.point z y)).fst) := by
    funext z
    exact JointSliceRegularity.gradient_x_slice_eq_projection J hJ z y
  rw [heq]
  exact hc

theorem gradient_x_hasFDerivAt_y
    (J : Joint E F → ℝ) (hC2 : ContDiff ℝ 2 J) (u : E) (y : F) :
    HasFDerivAt (fun z : F => gradient (fun t => JointSliceRegularity.curry J t z) u)
      (blockUY J (JointSliceRegularity.point u y)) y := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hgrad := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
    (JointSliceRegularity.point u y)).hasFDerivAt
  have hc := (WithLp.fstL 2 ℝ E F).hasFDerivAt.comp y
    (hgrad.comp y (JointSliceRegularity.point_hasFDerivAt_y u y))
  have heq : (fun z : F => gradient (fun t => JointSliceRegularity.curry J t z) u) =
      (fun z => (gradient J (JointSliceRegularity.point u z)).fst) := by
    funext z
    exact JointSliceRegularity.gradient_x_slice_eq_projection J hJ u z
  rw [heq]
  exact hc

theorem block_norm_bounds
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (u : E) (y : F) :
    ‖blockUU J (JointSliceRegularity.point u y)‖ ≤ L ∧
      ‖blockUY J (JointSliceRegularity.point u y)‖ ≤ L := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  exact ⟨(gradient_x_hasFDerivAt_x J hC2 u y).le_of_lip' hL.le
    (Filter.Eventually.of_forall (fun z =>
      JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip z u y)),
    (gradient_x_hasFDerivAt_y J hC2 u y).le_of_lip' hL.le
    (Filter.Eventually.of_forall (fun z =>
      JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u z y))⟩

theorem primalHessian_quadratic_bounds
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) (h : E) :
    L * ‖h‖ ^ 2 ≤ inner ℝ (primalHessian J L x y h) h ∧
      inner ℝ (primalHessian J L x y h) h ≤ 3 * L * ‖h‖ ^ 2 := by
  let H := blockUU J (JointSliceRegularity.point (primal J L x y) y)
  have hH := (block_norm_bounds J L hL hC2 hLip (primal J L x y) y).1
  have hv : ‖H h‖ ≤ L * ‖h‖ :=
    (H.le_opNorm h).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg h))
  have hi := abs_le.mp (abs_real_inner_le_norm (H h) h)
  have hm := mul_le_mul_of_nonneg_right hv (norm_nonneg h)
  change L * ‖h‖ ^ 2 ≤ inner ℝ (H h + (2 * L) • h) h ∧
    inner ℝ (H h + (2 * L) • h) h ≤ 3 * L * ‖h‖ ^ 2
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  constructor <;> nlinarith only [hi.1, hi.2, hm]

theorem primalHessian_norm_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) : ‖primalHessian J L x y‖ ≤ 3 * L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity : 0 ≤ 3 * L)
  intro h
  change ‖blockUU J (JointSliceRegularity.point (primal J L x y) y) h + (2 * L) • h‖ ≤ _
  have hH := (block_norm_bounds J L hL hC2 hLip (primal J L x y) y).1
  calc
    _ ≤ ‖blockUU J (JointSliceRegularity.point (primal J L x y) y) h‖ + ‖(2 * L) • h‖ := norm_add_le _ _
    _ ≤ L * ‖h‖ + (2 * L) * ‖h‖ := by
      gcongr
      · exact (ContinuousLinearMap.le_opNorm _ h).trans
          (mul_le_mul_of_nonneg_right hH (norm_nonneg h))
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * L)]
    _ = 3 * L * ‖h‖ := by ring

theorem primalHessian_inverse_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    (primalHessian J L x y).IsInvertible ∧ ‖(primalHessian J L x y).inverse‖ ≤ 1 / L := by
  have hc := fun h => (primalHessian_quadratic_bounds J L hL hC2 hLip x y h).1
  let A := OriginalCoerciveOperator.equivalenceOfCoercive (primalHessian J L x y) L hL hc
  have hA : A.toContinuousLinearMap = primalHessian J L x y := rfl
  refine ⟨⟨A, hA⟩, ?_⟩
  rw [← hA, ContinuousLinearMap.inverse_equiv]
  exact OriginalCoerciveOperator.inverse_norm_le (primalHessian J L x y) L hL hc

theorem primalHessian_condition_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    ‖primalHessian J L x y‖ * ‖(primalHessian J L x y).inverse‖ ≤ 3 := by
  have h1 := primalHessian_norm_bound J L hL hC2 hLip x y
  have h2 := (primalHessian_inverse_bound J L hL hC2 hLip x y).2
  calc
    _ ≤ (3 * L) * (1 / L) := by gcongr
    _ = 3 := by field_simp


noncomputable def residualDerivative (J : Joint E F → ℝ) (L : ℝ) (p : F × E) : F × E →L[ℝ] E :=
  (blockUY J (JointSliceRegularity.point p.2 p.1)).comp (ContinuousLinearMap.fst ℝ F E) +
    (blockUU J (JointSliceRegularity.point p.2 p.1) + (2 * L) • ContinuousLinearMap.id ℝ E).comp
      (ContinuousLinearMap.snd ℝ F E)

theorem residual_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (x : E) (hC2 : ContDiff ℝ 2 J) :
    ContDiff ℝ 1 (residual J L x) := by
  have hemb : ContDiff ℝ 1 (fun p : F × E => JointSliceRegularity.point p.2 p.1) :=
    ((JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.contDiff.comp contDiff_snd).add
      ((JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap.contDiff.comp contDiff_fst)
  have hgrad := (WithLp.fstL 2 ℝ E F).contDiff.comp
    ((contDiff_gradient_of_contDiff2 J hC2).comp hemb)
  have hlin : ContDiff ℝ 1 (fun p : F × E => p.2 - x) := contDiff_snd.sub contDiff_const
  exact hgrad.add (hlin.const_smul (2 * L))

theorem residual_hasFDerivAt
    (J : Joint E F → ℝ) (L : ℝ) (x : E) (hC2 : ContDiff ℝ 2 J) (p : F × E) :
    HasFDerivAt (residual J L x) (residualDerivative J L p) p := by
  let emb : F × E →L[ℝ] Joint E F :=
    (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.comp
        (ContinuousLinearMap.snd ℝ F E) +
      (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap.comp
        (ContinuousLinearMap.fst ℝ F E)
  have hemb : HasFDerivAt (fun p : F × E => JointSliceRegularity.point p.2 p.1) emb p :=
    emb.hasFDerivAt
  have hgrad := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
    (JointSliceRegularity.point p.2 p.1)).hasFDerivAt
  have hc := (WithLp.fstL 2 ℝ E F).hasFDerivAt.comp p (hgrad.comp p hemb)
  have hlin : HasFDerivAt (fun p : F × E => (2 * L) • (p.2 - x))
      ((2 * L) • ContinuousLinearMap.snd ℝ F E) p :=
    ((ContinuousLinearMap.snd ℝ F E).hasFDerivAt.sub_const x).const_smul (2 * L)
  convert! hc.add hlin using 1
  ext q <;>
    simp only [residualDerivative, blockUU, blockUY, emb,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      map_add] <;>
    module

theorem residual_zero_at_primal
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) : residual J L x (y, primal J L x y) = 0 := by
  have hfoc := primal_first_order J L hL hJ hLip x y
  unfold residual
  rw [← JointSliceRegularity.gradient_x_slice_eq_projection J hJ, hfoc]
  module

theorem primal_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : ContDiff ℝ 1 (primal J L x) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hpl : LipschitzWith 1 (primal J L x) := by
    apply LipschitzWith.of_dist_le_mul
    intro y y'
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using primal_lipschitz J L hL hJ hLip x y y'
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hinv : (fderiv ℝ (residual J L x) (y, primal J L x y) ∘L
      ContinuousLinearMap.inr ℝ F E).IsInvertible := by
    rw [(residual_hasFDerivAt J L x hC2 (y, primal J L x y)).fderiv]
    have heq : (residualDerivative J L (y, primal J L x y)).comp
        (ContinuousLinearMap.inr ℝ F E) = primalHessian J L x y := by
      ext h
      simp [residualDerivative, primalHessian]
    rw [heq]
    exact (primalHessian_inverse_bound J L hL hC2 hLip x y).1
  exact actual_selection_contDiffAt (residual J L x) (primal J L x) y
    (residual_contDiff J L x hC2).contDiffAt hinv hpl.continuous.continuousAt
    (residual_zero_at_primal J L hL hJ hLip x)

theorem primal_derivative_formula
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    fderiv ℝ (primal J L x) y = -(primalHessian J L x y).inverse.comp
      (blockUY J (JointSliceRegularity.point (primal J L x y) y)) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hu := ((primal_contDiff J L hL hC2 hLip x).differentiable (by norm_num) y).hasFDerivAt
  have hc := (residual_hasFDerivAt J L x hC2 (y, primal J L x y)).comp y
    ((hasFDerivAt_id y).prodMk hu)
  have heq : (fun t : F => residual J L x (t, primal J L x t)) = fun _ => (0 : E) := by
    funext t
    exact residual_zero_at_primal J L hL hJ hLip x t
  change HasFDerivAt (fun t : F => residual J L x (t, primal J L x t)) _ y at hc
  rw [heq] at hc
  have hd := hc.unique (hasFDerivAt_const (c := (0 : E)) y)
  have hi := (primalHessian_inverse_bound J L hL hC2 hLip x y).1
  ext h
  have hh := DFunLike.congr_fun hd h
  change blockUY J (JointSliceRegularity.point (primal J L x y) y) h +
    primalHessian J L x y (fderiv ℝ (primal J L x) y h) = 0 at hh
  have hneg : primalHessian J L x y (fderiv ℝ (primal J L x) y h) =
      -blockUY J (JointSliceRegularity.point (primal J L x y) y) h := by
    rw [eq_neg_iff_add_eq_zero]
    simpa only [add_comm] using hh
  have hhInv := congrArg (primalHessian J L x y).inverse hneg
  simpa only [hi.inverse_apply_self, map_neg, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply] using hhInv

theorem primal_derivative_norm_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) : ‖fderiv ℝ (primal J L x) y‖ ≤ 1 := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hu := ((primal_contDiff J L hL hC2 hLip x).differentiable (by norm_num) y).hasFDerivAt
  exact hu.le_of_lip' (by norm_num)
    (Filter.Eventually.of_forall (fun t => by
      simpa only [one_mul] using primal_lipschitz J L hL hJ hLip x t y))

theorem primalHessian_selfadjoint
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J) (x : E) (y : F) :
    (primalHessian J L x y).adjoint = primalHessian J L x y := by
  have hs := OriginalSaddleTangent.gradient_derivative_selfadjoint
    (fun t => JointSliceRegularity.curry J t y)
    (JointSliceRegularity.contDiff2_x_slice J hC2 y) (primal J L x y)
  rw [(gradient_x_hasFDerivAt_x J hC2 (primal J L x y) y).fderiv] at hs
  simp only [primalHessian, map_add, map_smul, hs, ContinuousLinearMap.adjoint_id]


noncomputable def regularizedHessian (J : Joint E F → ℝ) (L : ℝ) (u : E) (y : F) : E →L[ℝ] E :=
  blockUU J (JointSliceRegularity.point u y) + (2 * L) • ContinuousLinearMap.id ℝ E

theorem regularizedHessian_quadratic_bounds
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (u : E) (y : F) (h : E) :
    L * ‖h‖ ^ 2 ≤ inner ℝ (regularizedHessian J L u y h) h ∧
      inner ℝ (regularizedHessian J L u y h) h ≤ 3 * L * ‖h‖ ^ 2 := by
  let H := blockUU J (JointSliceRegularity.point u y)
  have hH := (block_norm_bounds J L hL hC2 hLip u y).1
  have hv : ‖H h‖ ≤ L * ‖h‖ :=
    (H.le_opNorm h).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg h))
  have hi := abs_le.mp (abs_real_inner_le_norm (H h) h)
  have hm := mul_le_mul_of_nonneg_right hv (norm_nonneg h)
  change L * ‖h‖ ^ 2 ≤ inner ℝ (H h + (2 * L) • h) h ∧
    inner ℝ (H h + (2 * L) • h) h ≤ 3 * L * ‖h‖ ^ 2
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  constructor <;> nlinarith only [hi.1, hi.2, hm]

theorem regularizedHessian_norm_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (u : E) (y : F) : ‖regularizedHessian J L u y‖ ≤ 3 * L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity : 0 ≤ 3 * L)
  intro h
  change ‖blockUU J (JointSliceRegularity.point u y) h + (2 * L) • h‖ ≤ _
  have hH := (block_norm_bounds J L hL hC2 hLip u y).1
  calc
    _ ≤ ‖blockUU J (JointSliceRegularity.point u y) h‖ + ‖(2 * L) • h‖ := norm_add_le _ _
    _ ≤ L * ‖h‖ + (2 * L) * ‖h‖ := by
      gcongr
      · exact (ContinuousLinearMap.le_opNorm _ h).trans
          (mul_le_mul_of_nonneg_right hH (norm_nonneg h))
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * L)]
    _ = 3 * L * ‖h‖ := by ring

theorem regularizedHessian_inverse_and_condition
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (u : E) (y : F) :
    (regularizedHessian J L u y).IsInvertible ∧
      ‖(regularizedHessian J L u y).inverse‖ ≤ 1 / L ∧
      ‖regularizedHessian J L u y‖ * ‖(regularizedHessian J L u y).inverse‖ ≤ 3 := by
  have hc := fun h => (regularizedHessian_quadratic_bounds J L hL hC2 hLip u y h).1
  let A := OriginalCoerciveOperator.equivalenceOfCoercive (regularizedHessian J L u y) L hL hc
  have hA : A.toContinuousLinearMap = regularizedHessian J L u y := rfl
  have hi : ‖(regularizedHessian J L u y).inverse‖ ≤ 1 / L := by
    rw [← hA, ContinuousLinearMap.inverse_equiv]
    exact OriginalCoerciveOperator.inverse_norm_le _ L hL hc
  refine ⟨⟨A, hA⟩, hi, ?_⟩
  have hn := regularizedHessian_norm_bound J L hL hC2 hLip u y
  calc
    _ ≤ (3 * L) * (1 / L) := by gcongr
    _ = 3 := by field_simp

/-- This principal contains all original conclusions for the actual selected minimizer,
plus existence/C1/invertibility certificates and uniform conditioning at all primal points. -/
theorem primal_elimination_from_standing_joint
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) :
    (∀ y : F,
      (∀ u : E, JointSliceRegularity.curry J (primal J L x y) y +
        L * ‖primal J L x y - x‖ ^ 2 ≤ JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2) ∧
      (∀ u : E, (∀ v : E, JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2 ≤
        JointSliceRegularity.curry J v y + L * ‖v - x‖ ^ 2) → u = primal J L x y)) ∧
    (∀ y : F, (primalHessian J L x y).adjoint = primalHessian J L x y) ∧
    (∀ y : F, ∀ h : E, L * ‖h‖ ^ 2 ≤ inner ℝ (primalHessian J L x y h) h ∧
      inner ℝ (primalHessian J L x y h) h ≤ 3 * L * ‖h‖ ^ 2) ∧
    (∀ y : F, ‖primalHessian J L x y‖ * ‖(primalHessian J L x y).inverse‖ ≤ 3) ∧
    ContDiff ℝ 1 (primal J L x) ∧
    (∀ y : F, fderiv ℝ (primal J L x) y = -(primalHessian J L x y).inverse.comp
      (blockUY J (JointSliceRegularity.point (primal J L x y) y))) ∧
    (∀ y : F, ‖fderiv ℝ (primal J L x) y‖ ≤ 1) ∧
    (∀ y y' : F, ‖JointSliceRegularity.point (primal J L x y) y -
      JointSliceRegularity.point (primal J L x y') y'‖ ≤ Real.sqrt 2 * ‖y - y'‖) ∧
    (∀ u : E, ∀ y : F, ∀ h : E,
      L * ‖h‖ ^ 2 ≤ inner ℝ (regularizedHessian J L u y h) h ∧
      inner ℝ (regularizedHessian J L u y h) h ≤ 3 * L * ‖h‖ ^ 2) ∧
    (∀ u : E, ∀ y : F, (regularizedHessian J L u y).IsInvertible ∧
      ‖(regularizedHessian J L u y).inverse‖ ≤ 1 / L ∧
      ‖regularizedHessian J L u y‖ * ‖(regularizedHessian J L u y).inverse‖ ≤ 3) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  exact ⟨primal_is_unique_minimizer J L hL hJ hLip x,
    primalHessian_selfadjoint J L hC2 x,
    primalHessian_quadratic_bounds J L hL hC2 hLip x,
    primalHessian_condition_bound J L hL hC2 hLip x,
    primal_contDiff J L hL hC2 hLip x,
    primal_derivative_formula J L hL hC2 hLip x,
    primal_derivative_norm_bound J L hL hC2 hLip x,
    primal_graph_lipschitz J L hL hJ hLip x,
    regularizedHessian_quadratic_bounds J L hL hC2 hLip,
    regularizedHessian_inverse_and_condition J L hL hC2 hLip⟩

end OriginalPrimalElimination
end

section
-- Source component: DualCurvature.lean

namespace OriginalDualCurvature

open OriginalSaddleImplicit
open OriginalPrimalElimination

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def graph (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) : Joint E F :=
  JointSliceRegularity.point (primal J L x y) y

noncomputable def psi (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) : ℝ :=
  -sInf (Set.range (fun u : E => JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2))

noncomputable def blockYU (J : Joint E F → ℝ) (w : Joint E F) : E →L[ℝ] F :=
  (WithLp.sndL 2 ℝ E F).comp
    ((fderiv ℝ (gradient J) w).comp (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap)

noncomputable def blockYY (J : Joint E F → ℝ) (w : Joint E F) : F →L[ℝ] F :=
  (WithLp.sndL 2 ℝ E F).comp
    ((fderiv ℝ (gradient J) w).comp (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap)

noncomputable def schur (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) : F →L[ℝ] F :=
  -blockYY J (graph J L x y) + (blockYU J (graph J L x y)).comp
    ((primalHessian J L x y).inverse.comp (blockUY J (graph J L x y)))

theorem psi_eq_value_at_primal
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    psi J L x y = -(J (graph J L x y) + L * ‖primal J L x y - x‖ ^ 2) := by
  change -MoreauTransfer.envelope (fun u => JointSliceRegularity.curry J u y) L x = _
  rw [MoreauTransfer.envelope_eq_prox_objective _ L hL
    (JointSliceRegularity.differentiable_x_slice J hJ y)
    (slice_weak_convex J L hL hJ hLip y) x]
  rfl

theorem graph_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : ContDiff ℝ 1 (graph J L x) := by
  exact ((JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.contDiff.comp
    (primal_contDiff J L hL hC2 hLip x)).add
      (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap.contDiff

theorem graph_hasFDerivAt
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    HasFDerivAt (graph J L x)
      ((JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.comp
        (fderiv ℝ (primal J L x) y) +
          (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap) y := by
  have hu := ((primal_contDiff J L hL hC2 hLip x).differentiable (by norm_num) y).hasFDerivAt
  exact ((JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.hasFDerivAt.comp y hu).add
    (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap.hasFDerivAt

theorem psi_hasGradientAt
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    HasGradientAt (psi J L x) (-(gradient J (graph J L x y)).snd) y := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hu := ((primal_contDiff J L hL hC2 hLip x).differentiable (by norm_num) y).hasFDerivAt
  have hjcomp := (hJ (graph J L x y)).hasFDerivAt.comp y (graph_hasFDerivAt J L hL hC2 hLip x y)
  have hquad := ((hu.sub_const x).norm_sq).const_mul L
  have heq : psi J L x = fun t => -(J (graph J L x t) + L * ‖primal J L x t - x‖ ^ 2) := by
    funext t
    exact psi_eq_value_at_primal J L hL hJ hLip x t
  have hfoc := primal_first_order J L hL hJ hLip x y
  rw [JointSliceRegularity.gradient_x_slice_eq_projection J hJ] at hfoc
  change (gradient J (graph J L x y)).fst = (2 * L) • (x - primal J L x y) at hfoc
  rw [heq]
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! (hjcomp.add hquad).neg using 1
  ext h
  simp only [InnerProductSpace.toDual_apply_apply, neg_apply, add_apply,
    ContinuousLinearMap.comp_apply, smul_apply, two_smul, smul_eq_mul]
  change inner ℝ (-(gradient J (graph J L x y)).snd) h =
    -((fderiv ℝ J (graph J L x y))
      (JointSliceRegularity.axisX (fderiv ℝ (primal J L x) y h) + JointSliceRegularity.axisY h) +
        L * (inner ℝ (primal J L x y - x) (fderiv ℝ (primal J L x) y h) +
          inner ℝ (primal J L x y - x) (fderiv ℝ (primal J L x) y h)))
  rw [← inner_gradient_left, inner_add_right, JointSliceRegularity.inner_axisX,
    JointSliceRegularity.inner_axisY, hfoc, real_inner_smul_left, inner_neg_left]
  rw [show primal J L x y - x = -(x - primal J L x y) by abel, inner_neg_left]
  ring

theorem psi_gradient
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : gradient (psi J L x) = fun y => -(gradient J (graph J L x y)).snd := by
  funext y
  exact (psi_hasGradientAt J L hL hC2 hLip x y).gradient

theorem psi_gradient_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : ContDiff ℝ 1 (gradient (psi J L x)) := by
  rw [psi_gradient J L hL hC2 hLip x]
  exact ((WithLp.sndL 2 ℝ E F).contDiff.comp
    ((contDiff_gradient_of_contDiff2 J hC2).comp (graph_contDiff J L hL hC2 hLip x))).neg


theorem psi_gradient_hasFDerivAt
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    HasFDerivAt (gradient (psi J L x)) (schur J L x y) y := by
  have hg := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
    (graph J L x y)).hasFDerivAt
  have hc := ((WithLp.sndL 2 ℝ E F).hasFDerivAt.comp y
    (hg.comp y (graph_hasFDerivAt J L hL hC2 hLip x y))).neg
  rw [psi_gradient J L hL hC2 hLip x]
  convert! hc using 1
  ext h
  rw [primal_derivative_formula J L hL hC2 hLip x y]
  simp only [schur, blockYY, blockYU, graph, ContinuousLinearMap.comp_apply,
    add_apply, neg_apply, map_add, map_neg]
  module

theorem psi_hessian_formula
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) : fderiv ℝ (gradient (psi J L x)) y = schur J L x y :=
  (psi_gradient_hasFDerivAt J L hL hC2 hLip x y).fderiv

theorem psi_contDiff2
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : ContDiff ℝ 2 (psi J L x) := by
  have hdiff : Differentiable ℝ (psi J L x) :=
    fun y => (psi_hasGradientAt J L hL hC2 hLip x y).differentiableAt
  have hfd : fderiv ℝ (psi J L x) = fun y =>
      InnerProductSpace.toDual ℝ F (gradient (psi J L x) y) := by
    funext y
    exact toDual_gradient.symm
  have hc : ContDiff ℝ 1 (fderiv ℝ (psi J L x)) := by
    rw [hfd]
    exact (InnerProductSpace.toDual ℝ F).toContinuousLinearEquiv.contDiff.comp
      (psi_gradient_contDiff J L hL hC2 hLip x)
  exact contDiff_succ_iff_fderiv.mpr ⟨hdiff, by simp, hc⟩

theorem cross_blocks_adjoint
    (J : Joint E F → ℝ) (hC2 : ContDiff ℝ 2 J) (w : Joint E F) :
    blockYU J w = (blockUY J w).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro e f
  let H := fderiv ℝ (gradient J) w
  have hself : H.adjoint = H := OriginalSaddleTangent.gradient_derivative_selfadjoint J hC2 w
  change inner ℝ (H (JointSliceRegularity.axisX e)).snd f =
    inner ℝ e (H (JointSliceRegularity.axisY f)).fst
  calc
    inner ℝ (H (JointSliceRegularity.axisX e)).snd f =
        inner ℝ (H (JointSliceRegularity.axisX e)) (JointSliceRegularity.axisY f) :=
      (JointSliceRegularity.inner_axisY _ _).symm
    _ = inner ℝ (JointSliceRegularity.axisX e) (H (JointSliceRegularity.axisY f)) := by
      rw [← H.adjoint_inner_right, hself]
    _ = inner ℝ (H (JointSliceRegularity.axisY f)) (JointSliceRegularity.axisX e) := real_inner_comm _ _
    _ = inner ℝ (H (JointSliceRegularity.axisY f)).fst e := JointSliceRegularity.inner_axisX _ _
    _ = inner ℝ e (H (JointSliceRegularity.axisY f)).fst := real_inner_comm _ _

theorem gradient_y_hasFDerivAt_y
    (J : Joint E F → ℝ) (hC2 : ContDiff ℝ 2 J) (u : E) (y : F) :
    HasFDerivAt (gradient (JointSliceRegularity.curry J u))
      (blockYY J (JointSliceRegularity.point u y)) y := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hgrad := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
    (JointSliceRegularity.point u y)).hasFDerivAt
  have hc := (WithLp.sndL 2 ℝ E F).hasFDerivAt.comp y
    (hgrad.comp y (JointSliceRegularity.point_hasFDerivAt_y u y))
  have heq : gradient (JointSliceRegularity.curry J u) =
      (fun z => (gradient J (JointSliceRegularity.point u z)).snd) := by
    funext z
    exact JointSliceRegularity.gradient_y_slice_eq_projection J hJ u z
  rw [heq]
  exact hc

theorem blockYY_norm_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (u : E) (y : F) : ‖blockYY J (JointSliceRegularity.point u y)‖ ≤ L := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  exact (gradient_y_hasFDerivAt_y J hC2 u y).le_of_lip' hL.le
    (Filter.Eventually.of_forall (fun z =>
      JointSliceRegularity.gradient_y_lipschitz_in_y J hJ L hLip u z y))


theorem negative_blockYY_lower_bound
    (J : Joint E F → ℝ) (μ : ℝ) (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J u y))
    (u : E) (y h : F) :
    μ * ‖h‖ ^ 2 ≤ inner ℝ (-(blockYY J (JointSliceRegularity.point u y) h)) h := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hd := JointSliceRegularity.differentiable_y_slice J hJ u
  have hneg : gradient (fun t => -JointSliceRegularity.curry J u t) =
      fun t => -gradient (JointSliceRegularity.curry J u) t := by
    funext t
    exact OriginalSaddleRegularity.gradient_neg_of_differentiable _ hd t
  have hD : HasFDerivAt (gradient (fun t => -JointSliceRegularity.curry J u t))
      (-blockYY J (JointSliceRegularity.point u y)) y := by
    rw [hneg]
    exact (gradient_y_hasFDerivAt_y J hC2 u y).neg
  exact OriginalCoerciveOperator.derivative_coercive_of_strong_monotonicity _ μ
    (PacketCore.gradient_strong_monotone _ μ (hsc u) hd.neg) y _ hD h

theorem schur_quadratic_lower_bound
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) (y h : F) : μ * ‖h‖ ^ 2 ≤ inner ℝ (schur J L x y h) h := by
  let A := primalHessian J L x y
  let U := blockUY J (graph J L x y)
  let a := A.inverse (U h)
  have hi := (primalHessian_inverse_bound J L hL hC2 hLip x y).1
  have hAa : A a = U h := hi.self_apply_inverse _
  have ha := (primalHessian_quadratic_bounds J L hL hC2 hLip x y a).1
  have hpos : 0 ≤ inner ℝ (blockYU J (graph J L x y) a) h := by
    rw [cross_blocks_adjoint J hC2]
    change 0 ≤ inner ℝ (U.adjoint a) h
    rw [U.adjoint_inner_left, ← hAa]
    have heq : inner ℝ a (A a) = inner ℝ (A a) a := real_inner_comm _ _
    rw [heq]
    exact (by positivity : 0 ≤ L * ‖a‖ ^ 2).trans ha
  have hy := negative_blockYY_lower_bound J μ hC2 hsc (primal J L x y) y h
  change μ * ‖h‖ ^ 2 ≤ inner ℝ (-(blockYY J (graph J L x y) h) +
    blockYU J (graph J L x y) a) h
  rw [inner_add_left]
  exact hy.trans (le_add_of_nonneg_right hpos)

theorem schur_norm_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) : ‖schur J L x y‖ ≤ 2 * L := by
  have huu : ‖blockUY J (graph J L x y)‖ ≤ L :=
    (block_norm_bounds J L hL hC2 hLip (primal J L x y) y).2
  have hyy : ‖blockYY J (graph J L x y)‖ ≤ L :=
    blockYY_norm_bound J L hL hC2 hLip (primal J L x y) y
  have hyu : ‖blockYU J (graph J L x y)‖ ≤ L := by
    rw [cross_blocks_adjoint J hC2, ContinuousLinearMap.adjoint.norm_map]
    exact huu
  have hi := (primalHessian_inverse_bound J L hL hC2 hLip x y).2
  have ht : ‖(blockYU J (graph J L x y)).comp
      ((primalHessian J L x y).inverse.comp (blockUY J (graph J L x y)))‖ ≤ L := by
    calc
      _ ≤ ‖blockYU J (graph J L x y)‖ *
          (‖(primalHessian J L x y).inverse‖ * ‖blockUY J (graph J L x y)‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ L * ((1 / L) * L) := by gcongr
      _ = L := by field_simp
  calc
    _ ≤ ‖-blockYY J (graph J L x y)‖ + ‖(blockYU J (graph J L x y)).comp
        ((primalHessian J L x y).inverse.comp (blockUY J (graph J L x y)))‖ := norm_add_le _ _
    _ ≤ L + L := add_le_add (by rw [norm_neg]; exact hyy) ht
    _ = 2 * L := by ring

theorem psi_hessian_quadratic_bounds
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) (y h : F) :
    μ * ‖h‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient (psi J L x)) y h) h ∧
      inner ℝ (fderiv ℝ (gradient (psi J L x)) y h) h ≤ 2 * L * ‖h‖ ^ 2 := by
  rw [psi_hessian_formula J L hL hC2 hLip]
  refine ⟨schur_quadratic_lower_bound J L μ hL hC2 hLip hsc x y h, ?_⟩
  have hn := schur_norm_bound J L hL hC2 hLip x y
  calc
    _ ≤ ‖schur J L x y h‖ * ‖h‖ := real_inner_le_norm _ _
    _ ≤ (2 * L * ‖h‖) * ‖h‖ := mul_le_mul_of_nonneg_right
      ((ContinuousLinearMap.le_opNorm _ h).trans
        (mul_le_mul_of_nonneg_right hn (norm_nonneg h))) (norm_nonneg h)
    _ = 2 * L * ‖h‖ ^ 2 := by ring


theorem contracted_operator_norm
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : Z →L[ℝ] X) (Q : Y →L[ℝ] Z) (D : Z →L[ℝ] Z)
    (hP : ∀ z : Z, ‖P z‖ ≤ ‖z‖) (hQ : ∀ y : Y, ‖Q y‖ ≤ ‖y‖) :
    ‖P.comp (D.comp Q)‖ ≤ ‖D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
  intro h
  exact (hP _).trans ((D.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (hQ h) (norm_nonneg D)))

theorem contracted_operator_difference_norm
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : Z →L[ℝ] X) (Q : Y →L[ℝ] Z) (D D' : Z →L[ℝ] Z)
    (hP : ∀ z : Z, ‖P z‖ ≤ ‖z‖) (hQ : ∀ y : Y, ‖Q y‖ ≤ ‖y‖) :
    ‖P.comp (D.comp Q) - P.comp (D'.comp Q)‖ ≤ ‖D - D'‖ := by
  have heq : P.comp (D.comp Q) - P.comp (D'.comp Q) = P.comp ((D - D').comp Q) := by
    ext h
    simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub]
  rw [heq]
  exact contracted_operator_norm P Q (D - D') hP hQ

theorem block_difference_bounds
    (J : Joint E F → ℝ) (w w' : Joint E F) :
    ‖blockUU J w - blockUU J w'‖ ≤ ‖fderiv ℝ (gradient J) w - fderiv ℝ (gradient J) w'‖ ∧
    ‖blockUY J w - blockUY J w'‖ ≤ ‖fderiv ℝ (gradient J) w - fderiv ℝ (gradient J) w'‖ ∧
    ‖blockYU J w - blockYU J w'‖ ≤ ‖fderiv ℝ (gradient J) w - fderiv ℝ (gradient J) w'‖ ∧
    ‖blockYY J w - blockYY J w'‖ ≤ ‖fderiv ℝ (gradient J) w - fderiv ℝ (gradient J) w'‖ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact contracted_operator_difference_norm _ _ _ _
      (JointSliceRegularity.norm_fst_projection) (fun h => le_of_eq ((JointSliceRegularity.axisX (E := E) (F := F)).norm_map h))
  · exact contracted_operator_difference_norm _ _ _ _
      (JointSliceRegularity.norm_fst_projection) (fun h => le_of_eq ((JointSliceRegularity.axisY (E := E) (F := F)).norm_map h))
  · exact contracted_operator_difference_norm _ _ _ _
      (JointSliceRegularity.norm_snd_projection) (fun h => le_of_eq ((JointSliceRegularity.axisX (E := E) (F := F)).norm_map h))
  · exact contracted_operator_difference_norm _ _ _ _
      (JointSliceRegularity.norm_snd_projection) (fun h => le_of_eq ((JointSliceRegularity.axisY (E := E) (F := F)).norm_map h))

theorem inverse_difference_norm_of_isInvertible
    (A B : E →L[ℝ] E) (hA : A.IsInvertible) (hB : B.IsInvertible) :
    ‖A.inverse - B.inverse‖ ≤ ‖A.inverse‖ * ‖B - A‖ * ‖B.inverse‖ := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  rw [← ha, ← hb, ContinuousLinearMap.inverse_equiv, ContinuousLinearMap.inverse_equiv]
  exact OriginalCoerciveOperator.inverse_difference_norm a b

theorem three_factor_norm
    (P : E →L[ℝ] F) (A : E →L[ℝ] E) (Q : F →L[ℝ] E) :
    ‖P.comp (A.comp Q)‖ ≤ ‖P‖ * ‖A‖ * ‖Q‖ := by
  calc
    _ ≤ ‖P‖ * (‖A‖ * ‖Q‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = _ := by ring

theorem three_factor_difference
    (P P' : E →L[ℝ] F) (A A' : E →L[ℝ] E) (Q Q' : F →L[ℝ] E) :
    P.comp (A.comp Q) - P'.comp (A'.comp Q') =
      (P - P').comp (A.comp Q) + P'.comp ((A - A').comp Q) +
        P'.comp (A'.comp (Q - Q')) := by
  ext h
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply, map_add, map_sub]
  abel


theorem schur_lipschitz_before_graph
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖schur J L x y - schur J L x y'‖ ≤ 4 * ρ * ‖graph J L x y - graph J L x y'‖ := by
  let d := ρ * ‖graph J L x y - graph J L x y'‖
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let P := blockYU J (graph J L x y)
  let P' := blockYU J (graph J L x y')
  let Q := blockUY J (graph J L x y)
  let Q' := blockUY J (graph J L x y')
  let A := primalHessian J L x y
  let A' := primalHessian J L x y'
  have hQ : ‖Q‖ ≤ L := (block_norm_bounds J L hL hC2 hLip (primal J L x y) y).2
  have hQ' : ‖Q'‖ ≤ L := (block_norm_bounds J L hL hC2 hLip (primal J L x y') y').2
  have hP : ‖P‖ ≤ L := by
    dsimp [P]; rw [cross_blocks_adjoint J hC2, ContinuousLinearMap.adjoint.norm_map]; exact hQ
  have hP' : ‖P'‖ ≤ L := by
    dsimp [P']; rw [cross_blocks_adjoint J hC2, ContinuousLinearMap.adjoint.norm_map]; exact hQ'
  have hAi := primalHessian_inverse_bound J L hL hC2 hLip x y
  have hAi' := primalHessian_inverse_bound J L hL hC2 hLip x y'
  have hAiNorm : ‖A.inverse‖ ≤ 1 / L := hAi.2
  have hAiNorm' : ‖A'.inverse‖ ≤ 1 / L := hAi'.2
  have hblocks := block_difference_bounds J (graph J L x y) (graph J L x y')
  have hH := hHess (graph J L x y) (graph J L x y')
  have hPdiff : ‖P - P'‖ ≤ d := hblocks.2.2.1.trans hH
  have hQdiff : ‖Q - Q'‖ ≤ d := hblocks.2.1.trans hH
  have hYYdiff : ‖blockYY J (graph J L x y) - blockYY J (graph J L x y')‖ ≤ d :=
    hblocks.2.2.2.trans hH
  have hAdiff : ‖A - A'‖ ≤ d := by
    have heq : A - A' = blockUU J (graph J L x y) - blockUU J (graph J L x y') := by
      dsimp [A, A', primalHessian, graph]
      abel
    rw [heq]
    exact hblocks.1.trans hH
  have hAiDiff : ‖A.inverse - A'.inverse‖ ≤ d / L ^ 2 := by
    calc
      _ ≤ ‖A.inverse‖ * ‖A' - A‖ * ‖A'.inverse‖ :=
        inverse_difference_norm_of_isInvertible A A' hAi.1 hAi'.1
      _ ≤ (1 / L) * d * (1 / L) := by
        rw [norm_sub_rev A' A]
        gcongr
      _ = d / L ^ 2 := by field_simp <;> ring
  have ht1 : ‖(P - P').comp (A.inverse.comp Q)‖ ≤ d := by
    calc
      _ ≤ ‖P - P'‖ * ‖A.inverse‖ * ‖Q‖ := three_factor_norm _ _ _
      _ ≤ d * (1 / L) * L := by gcongr
      _ = d := by field_simp
  have ht2 : ‖P'.comp ((A.inverse - A'.inverse).comp Q)‖ ≤ d := by
    calc
      _ ≤ ‖P'‖ * ‖A.inverse - A'.inverse‖ * ‖Q‖ := three_factor_norm _ _ _
      _ ≤ L * (d / L ^ 2) * L := by gcongr
      _ = d := by field_simp <;> ring
  have ht3 : ‖P'.comp (A'.inverse.comp (Q - Q'))‖ ≤ d := by
    calc
      _ ≤ ‖P'‖ * ‖A'.inverse‖ * ‖Q - Q'‖ := three_factor_norm _ _ _
      _ ≤ L * (1 / L) * d := by gcongr
      _ = d := by field_simp
  have hterms : ‖P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')‖ ≤ 3 * d := by
    rw [three_factor_difference]
    calc
      _ ≤ ‖(P - P').comp (A.inverse.comp Q)‖ +
          ‖P'.comp ((A.inverse - A'.inverse).comp Q)‖ +
          ‖P'.comp (A'.inverse.comp (Q - Q'))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ d + d + d := add_le_add (add_le_add ht1 ht2) ht3
      _ = 3 * d := by ring
  have heq : schur J L x y - schur J L x y' =
      -(blockYY J (graph J L x y) - blockYY J (graph J L x y')) +
        (P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')) := by
    dsimp [schur, P, P', Q, Q', A, A']
    abel
  rw [heq]
  calc
    _ ≤ ‖-(blockYY J (graph J L x y) - blockYY J (graph J L x y'))‖ +
        ‖P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')‖ := norm_add_le _ _
    _ ≤ d + 3 * d := add_le_add (by rw [norm_neg]; exact hYYdiff) hterms
    _ = 4 * ρ * ‖graph J L x y - graph J L x y'‖ := by dsimp [d]; ring

theorem psi_hessian_lipschitz
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖fderiv ℝ (gradient (psi J L x)) y - fderiv ℝ (gradient (psi J L x)) y'‖ ≤
      (4 * Real.sqrt 2) * ρ * ‖y - y'‖ := by
  rw [psi_hessian_formula J L hL hC2 hLip x y, psi_hessian_formula J L hL hC2 hLip x y']
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hgraph := primal_graph_lipschitz J L hL hJ hLip x y y'
  calc
    _ ≤ 4 * ρ * ‖graph J L x y - graph J L x y'‖ :=
      schur_lipschitz_before_graph J L ρ hL hρ hC2 hLip hHess x y y'
    _ ≤ 4 * ρ * (Real.sqrt 2 * ‖y - y'‖) :=
      mul_le_mul_of_nonneg_left hgraph (by positivity : 0 ≤ 4 * ρ)
    _ = (4 * Real.sqrt 2) * ρ * ‖y - y'‖ := by ring


theorem psi_gradient_slice
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    gradient (psi J L x) y = -gradient (JointSliceRegularity.curry J (primal J L x y)) y := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  rw [psi_gradient J L hL hC2 hLip x,
    JointSliceRegularity.gradient_y_slice_eq_projection J hJ]
  rfl

theorem psi_gradient_lipschitz
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : ∀ y y' : F,
    ‖gradient (psi J L x) y - gradient (psi J L x) y'‖ ≤ 2 * L * ‖y - y'‖ := by
  apply OriginalAudit.lipschitz_gradient_of_bounded_fderiv_gradient
  · exact (psi_gradient_contDiff J L hL hC2 hLip x).differentiable (by norm_num)
  · intro y
    rw [psi_hessian_formula J L hL hC2 hLip x y]
    exact schur_norm_bound J L hL hC2 hLip x y

theorem psi_strongConvex
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) : StrongConvexOn (Set.univ : Set F) μ (psi J L x) := by
  let g : F → E → ℝ := fun y u => -(JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2)
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hw : ∀ u : E, StrongConvexOn (Set.univ : Set F) (-(-μ)) (fun y => g y u) := by
    intro u
    apply strongConvexOn_iff_convex.mpr
    have hc := (strongConvexOn_iff_convex.mp (hsc u)).add_const (-L * ‖u - x‖ ^ 2)
    convert hc using 1 <;> (first | rfl | (funext y; dsimp [g]; ring))
  have hmax : ∀ y : F, ∀ u : E, g y u ≤ g y (primal J L x y) := by
    intro y u
    exact neg_le_neg ((primal_is_unique_minimizer J L hL hJ hLip x y).1 u)
  have hv := OriginalSaddleRegularity.value_weakly_convex_from_actual_maxima
    g (-μ) hw (primal J L x) hmax
  have heq : OriginalSaddleRegularity.value g (primal J L x) = psi J L x := by
    funext y
    exact (psi_eq_value_at_primal J L hL hJ hLip x y).symm
  rw [heq] at hv
  simpa only [neg_neg] using hv

/-- All original reduced-dual curvature conclusions refer to the genuine negative minimum,
with actual gradients/Hessians and no value-function or Schur formula assumptions. -/
theorem dual_curvature_from_standing_joint
    (J : Joint E F → ℝ) (L μ ρ : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (hconcave : ∀ u : E, StrongConcaveOn (Set.univ : Set F) μ
      (fun y => J (WithLp.toLp 2 (u, y))))
    (x : E) :
    ContDiff ℝ 2 (psi J L x) ∧
    (∀ y : F, gradient (psi J L x) y = -gradient (JointSliceRegularity.curry J (primal J L x y)) y) ∧
    (∀ y : F, fderiv ℝ (gradient (psi J L x)) y =
      -blockYY J (graph J L x y) + (blockYU J (graph J L x y)).comp
        ((primalHessian J L x y).inverse.comp (blockUY J (graph J L x y)))) ∧
    (∀ y : F, ∀ h : F,
      μ * ‖h‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient (psi J L x)) y h) h ∧
      inner ℝ (fderiv ℝ (gradient (psi J L x)) y h) h ≤ 2 * L * ‖h‖ ^ 2) ∧
    (∀ y y' : F,
      ‖fderiv ℝ (gradient (psi J L x)) y - fderiv ℝ (gradient (psi J L x)) y'‖ ≤
        (4 * Real.sqrt 2) * ρ * ‖y - y'‖) ∧
    StrongConvexOn (Set.univ : Set F) μ (psi J L x) ∧
    (∀ y y' : F, ‖gradient (psi J L x) y - gradient (psi J L x) y'‖ ≤ 2 * L * ‖y - y'‖) := by
  have hconcave' : ∀ u : E, StrongConcaveOn (Set.univ : Set F) μ (JointSliceRegularity.curry J u) := by
    intro u
    have heq : JointSliceRegularity.curry J u = (fun y : F => J (WithLp.toLp 2 (u, y))) := by
      funext y
      exact congrArg J (JointSliceRegularity.point_eq_toLp u y)
    rw [heq]
    exact hconcave u
  have hsc := JointSliceRegularity.strongConvex_negative_y_slice J μ hconcave'
  exact ⟨psi_contDiff2 J L hL hC2 hLip x,
    psi_gradient_slice J L hL hC2 hLip x,
    psi_hessian_formula J L hL hC2 hLip x,
    psi_hessian_quadratic_bounds J L μ hL hC2 hLip hsc x,
    psi_hessian_lipschitz J L ρ hL hρ hC2 hLip hHess x,
    psi_strongConvex J L μ hL hC2 hLip hsc x,
    psi_gradient_lipschitz J L hL hC2 hLip x⟩

end OriginalDualCurvature
end

section
-- Source component: DualOracleEstimates.lean

namespace OriginalDualOracleEstimates

open OriginalSaddleImplicit
open OriginalPrimalElimination
open OriginalDualCurvature

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def schurAt (J : Joint E F → ℝ) (L : ℝ) (u : E) (y : F) : F →L[ℝ] F :=
  -blockYY J (JointSliceRegularity.point u y) + (blockYU J (JointSliceRegularity.point u y)).comp
    ((regularizedHessian J L u y).inverse.comp (blockUY J (JointSliceRegularity.point u y)))

theorem off_solution_schur_lipschitz
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (u u' : E) (y y' : F) :
    ‖schurAt J L u y - schurAt J L u' y'‖ ≤ 4 * ρ * ‖JointSliceRegularity.point u y - JointSliceRegularity.point u' y'‖ := by
  let d := ρ * ‖JointSliceRegularity.point u y - JointSliceRegularity.point u' y'‖
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let P := blockYU J (JointSliceRegularity.point u y)
  let P' := blockYU J (JointSliceRegularity.point u' y')
  let Q := blockUY J (JointSliceRegularity.point u y)
  let Q' := blockUY J (JointSliceRegularity.point u' y')
  let A := regularizedHessian J L u y
  let A' := regularizedHessian J L u' y'
  have hQ : ‖Q‖ ≤ L := (block_norm_bounds J L hL hC2 hLip (u) y).2
  have hQ' : ‖Q'‖ ≤ L := (block_norm_bounds J L hL hC2 hLip (u') y').2
  have hP : ‖P‖ ≤ L := by
    dsimp [P]; rw [cross_blocks_adjoint J hC2, ContinuousLinearMap.adjoint.norm_map]; exact hQ
  have hP' : ‖P'‖ ≤ L := by
    dsimp [P']; rw [cross_blocks_adjoint J hC2, ContinuousLinearMap.adjoint.norm_map]; exact hQ'
  have hAi := regularizedHessian_inverse_and_condition J L hL hC2 hLip u y
  have hAi' := regularizedHessian_inverse_and_condition J L hL hC2 hLip u' y'
  have hAiNorm : ‖A.inverse‖ ≤ 1 / L := hAi.2.1
  have hAiNorm' : ‖A'.inverse‖ ≤ 1 / L := hAi'.2.1
  have hblocks := block_difference_bounds J (JointSliceRegularity.point u y) (JointSliceRegularity.point u' y')
  have hH := hHess (JointSliceRegularity.point u y) (JointSliceRegularity.point u' y')
  have hPdiff : ‖P - P'‖ ≤ d := hblocks.2.2.1.trans hH
  have hQdiff : ‖Q - Q'‖ ≤ d := hblocks.2.1.trans hH
  have hYYdiff : ‖blockYY J (JointSliceRegularity.point u y) - blockYY J (JointSliceRegularity.point u' y')‖ ≤ d :=
    hblocks.2.2.2.trans hH
  have hAdiff : ‖A - A'‖ ≤ d := by
    have heq : A - A' = blockUU J (JointSliceRegularity.point u y) - blockUU J (JointSliceRegularity.point u' y') := by
      dsimp [A, A', regularizedHessian]
      abel
    rw [heq]
    exact hblocks.1.trans hH
  have hAiDiff : ‖A.inverse - A'.inverse‖ ≤ d / L ^ 2 := by
    calc
      _ ≤ ‖A.inverse‖ * ‖A' - A‖ * ‖A'.inverse‖ :=
        inverse_difference_norm_of_isInvertible A A' hAi.1 hAi'.1
      _ ≤ (1 / L) * d * (1 / L) := by
        rw [norm_sub_rev A' A]
        gcongr
      _ = d / L ^ 2 := by field_simp <;> ring
  have ht1 : ‖(P - P').comp (A.inverse.comp Q)‖ ≤ d := by
    calc
      _ ≤ ‖P - P'‖ * ‖A.inverse‖ * ‖Q‖ := three_factor_norm _ _ _
      _ ≤ d * (1 / L) * L := by gcongr
      _ = d := by field_simp
  have ht2 : ‖P'.comp ((A.inverse - A'.inverse).comp Q)‖ ≤ d := by
    calc
      _ ≤ ‖P'‖ * ‖A.inverse - A'.inverse‖ * ‖Q‖ := three_factor_norm _ _ _
      _ ≤ L * (d / L ^ 2) * L := by gcongr
      _ = d := by field_simp <;> ring
  have ht3 : ‖P'.comp (A'.inverse.comp (Q - Q'))‖ ≤ d := by
    calc
      _ ≤ ‖P'‖ * ‖A'.inverse‖ * ‖Q - Q'‖ := three_factor_norm _ _ _
      _ ≤ L * (1 / L) * d := by gcongr
      _ = d := by field_simp
  have hterms : ‖P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')‖ ≤ 3 * d := by
    rw [three_factor_difference]
    calc
      _ ≤ ‖(P - P').comp (A.inverse.comp Q)‖ +
          ‖P'.comp ((A.inverse - A'.inverse).comp Q)‖ +
          ‖P'.comp (A'.inverse.comp (Q - Q'))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ d + d + d := add_le_add (add_le_add ht1 ht2) ht3
      _ = 3 * d := by ring
  have heq : schurAt J L u y - schurAt J L u' y' =
      -(blockYY J (JointSliceRegularity.point u y) - blockYY J (JointSliceRegularity.point u' y')) +
        (P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')) := by
    dsimp [schurAt, P, P', Q, Q', A, A']
    abel
  rw [heq]
  calc
    _ ≤ ‖-(blockYY J (JointSliceRegularity.point u y) - blockYY J (JointSliceRegularity.point u' y'))‖ +
        ‖P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')‖ := norm_add_le _ _
    _ ≤ d + 3 * d := add_le_add (by rw [norm_neg]; exact hYYdiff) hterms
    _ = 4 * ρ * ‖JointSliceRegularity.point u y - JointSliceRegularity.point u' y'‖ := by dsimp [d]; ring



noncomputable def valueEstimate (J : Joint E F → ℝ) (L : ℝ) (x u : E) (y : F) : ℝ :=
  -(JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2)

noncomputable def gradientEstimate (J : Joint E F → ℝ) (u : E) (y : F) : F :=
  -gradient (JointSliceRegularity.curry J u) y

theorem value_estimate_error
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    |valueEstimate J L x u y - psi J L x y| ≤ 3 * L / 2 * ‖u - primal J L x y‖ ^ 2 := by
  let p := primal J L x y
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hs := OriginalAudit.smooth_descent_upper (fun t => f t y) L hL
    (JointSliceRegularity.differentiable_x_slice J hJ y)
    (fun t t' => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip t t' y)
    p (u - p)
  rw [show p + (u - p) = u by abel] at hs
  have hfoc := primal_first_order J L hL hJ hLip x y
  change gradient (fun t => f t y) p = (2 * L) • (x - p) at hfoc
  rw [hfoc, real_inner_smul_left] at hs
  have hquad := OriginalSaddleStability.norm_square_center_change x p u
  have hquadL := congrArg (fun t : ℝ => L * t) hquad
  have hupper : f u y + L * ‖u - x‖ ^ 2 - (f p y + L * ‖p - x‖ ^ 2) ≤
      3 * L / 2 * ‖u - p‖ ^ 2 := by
    nlinarith only [hs, hquadL]
  have hmin := (primal_is_unique_minimizer J L hL hJ hLip x y).1 u
  have hnonneg : 0 ≤ f u y + L * ‖u - x‖ ^ 2 - (f p y + L * ‖p - x‖ ^ 2) := sub_nonneg.mpr hmin
  have heq : valueEstimate J L x u y - psi J L x y =
      -(f u y + L * ‖u - x‖ ^ 2 - (f p y + L * ‖p - x‖ ^ 2)) := by
    rw [psi_eq_value_at_primal J L hL hJ hLip x y]
    dsimp [valueEstimate, f, p, graph, JointSliceRegularity.curry]
    ring
  rw [heq, abs_neg, abs_of_nonneg hnonneg]
  exact hupper

theorem gradient_estimate_error
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    ‖gradientEstimate J u y - gradient (psi J L x) y‖ ≤ L * ‖u - primal J L x y‖ := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  rw [psi_gradient_slice J L hL hC2 hLip x y]
  change ‖-gradient (JointSliceRegularity.curry J u) y -
    -gradient (JointSliceRegularity.curry J (primal J L x y)) y‖ ≤ _
  have heq : -gradient (JointSliceRegularity.curry J u) y -
      -gradient (JointSliceRegularity.curry J (primal J L x y)) y =
    gradient (JointSliceRegularity.curry J (primal J L x y)) y -
      gradient (JointSliceRegularity.curry J u) y := by abel
  rw [heq]
  calc
    _ ≤ L * ‖primal J L x y - u‖ :=
      JointSliceRegularity.gradient_y_lipschitz_in_x J hJ L hLip (primal J L x y) u y
    _ = L * ‖u - primal J L x y‖ := by rw [norm_sub_rev]

theorem hessian_estimate_error
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u : E) (y : F) :
    ‖schurAt J L u y - fderiv ℝ (gradient (psi J L x)) y‖ ≤ 4 * ρ * ‖u - primal J L x y‖ := by
  rw [psi_hessian_formula J L hL hC2 hLip x y]
  have heq : schur J L x y = schurAt J L (primal J L x y) y := rfl
  rw [heq]
  have hb := off_solution_schur_lipschitz J L ρ hL hρ hC2 hLip hHess
    u (primal J L x y) y y
  rw [JointSliceRegularity.norm_point_sub_same_y] at hb
  exact hb

theorem plug_in_errors_at_tolerance
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u : E) (y : F) (e : ℝ) (he : ‖u - primal J L x y‖ ≤ e) :
    |valueEstimate J L x u y - psi J L x y| ≤ 3 * L / 2 * e ^ 2 ∧
    ‖gradientEstimate J u y - gradient (psi J L x) y‖ ≤ L * e ∧
    ‖schurAt J L u y - fderiv ℝ (gradient (psi J L x)) y‖ ≤ 4 * ρ * e := by
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  refine ⟨(value_estimate_error J L hL hC2 hLip x u y).trans ?_,
    (gradient_estimate_error J L hL hC2 hLip x u y).trans ?_,
    (hessian_estimate_error J L ρ hL hρ hC2 hLip hHess x u y).trans ?_⟩
  · exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) he0).mpr he) (by positivity)
  · exact mul_le_mul_of_nonneg_left he hL.le
  · exact mul_le_mul_of_nonneg_left he (by positivity)


theorem residual_strong_pairing
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    L * ‖u - primal J L x y‖ ^ 2 ≤
      inner ℝ (OriginalPrimalElimination.residual J L x (y, u)) (u - primal J L x y) := by
  let p := primal J L x y
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hs := OriginalSaddleRegularity.smooth_function_weakly_convex
    (fun t => f t y) L hL (JointSliceRegularity.differentiable_x_slice J hJ y)
    (fun t t' => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip t t' y)
  have he := PacketCore.gradient_strong_monotone (fun t => f t y) (-L) hs
    (JointSliceRegularity.differentiable_x_slice J hJ y) u p
  have hfoc := primal_first_order J L hL hJ hLip x y
  change gradient (fun t => f t y) p = (2 * L) • (x - p) at hfoc
  have hr : OriginalPrimalElimination.residual J L x (y, u) =
      gradient (fun t => f t y) u - gradient (fun t => f t y) p + (2 * L) • (u - p) := by
    dsimp only [OriginalPrimalElimination.residual]
    rw [← JointSliceRegularity.gradient_x_slice_eq_projection J hJ]
    change gradient (fun t => f t y) u + (2 * L) • (u - x) = _
    rw [hfoc]
    module
  rw [hr, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith only [he]

theorem observable_residual_distance
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    ‖u - primal J L x y‖ ≤ ‖OriginalPrimalElimination.residual J L x (y, u)‖ / L := by
  have hc := residual_strong_pairing J L hL hC2 hLip x u y
  have hi := real_inner_le_norm (OriginalPrimalElimination.residual J L x (y, u)) (u - primal J L x y)
  apply (le_div_iff₀ hL).mpr
  by_cases hz : ‖u - primal J L x y‖ = 0
  · rw [hz, zero_mul]; exact norm_nonneg _
  · have hp : 0 < ‖u - primal J L x y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact (mul_le_mul_iff_left₀ hp).mp (by nlinarith only [hc, hi])

theorem residual_norm_upper
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    ‖OriginalPrimalElimination.residual J L x (y, u)‖ ≤ 3 * L * ‖u - primal J L x y‖ := by
  let p := primal J L x y
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hfoc := primal_first_order J L hL hJ hLip x y
  change gradient (fun t => f t y) p = (2 * L) • (x - p) at hfoc
  have hr : OriginalPrimalElimination.residual J L x (y, u) =
      gradient (fun t => f t y) u - gradient (fun t => f t y) p + (2 * L) • (u - p) := by
    dsimp only [OriginalPrimalElimination.residual]
    rw [← JointSliceRegularity.gradient_x_slice_eq_projection J hJ]
    change gradient (fun t => f t y) u + (2 * L) • (u - x) = _
    rw [hfoc]
    module
  have hg := JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u p y
  rw [hr]
  calc
    _ ≤ ‖gradient (fun t => f t y) u - gradient (fun t => f t y) p‖ + ‖(2 * L) • (u - p)‖ := norm_add_le _ _
    _ ≤ L * ‖u - p‖ + (2 * L) * ‖u - p‖ := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * L)]
    _ = 3 * L * ‖u - p‖ := by ring

end OriginalDualOracleEstimates
end

section
-- Source component: DualOracleGD.lean

namespace OriginalDualOracleGD

open OriginalSaddleImplicit
open OriginalPrimalElimination
open OriginalDualCurvature
open OriginalDualOracleEstimates

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def step (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) (u : E) : E :=
  u - (1 / (9 * L)) • OriginalPrimalElimination.residual J L x (y, u)

noncomputable def iterate (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) (u0 : E) : ℕ → E :=
  Nat.rec u0 (fun _ u => step J L x y u)

noncomputable def logBudget (D e : ℝ) : ℕ := Nat.ceil (18 * Real.log (1 + 3 * D / e))

theorem step_squared_contraction
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    ‖step J L x y u - primal J L x y‖ ^ 2 ≤ (8 / 9 : ℝ) * ‖u - primal J L x y‖ ^ 2 := by
  let p := primal J L x y
  let r := OriginalPrimalElimination.residual J L x (y, u)
  let a : ℝ := 1 / (9 * L)
  have ha : 0 < a := by dsimp [a]; positivity
  have hc := residual_strong_pairing J L hL hC2 hLip x u y
  have hr := residual_norm_upper J L hL hC2 hLip x u y
  have hr2 : ‖r‖ ^ 2 ≤ (3 * L * ‖u - p‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * L * ‖u - p‖)).mpr hr
  have hn : step J L x y u - p = (u - p) - a • r := by dsimp [step, a, r]; abel
  rw [hn, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
    real_inner_smul_right, real_inner_comm r (u - p)]
  have hpos := mul_le_mul_of_nonneg_left hr2 (sq_nonneg a)
  have hneg := mul_le_mul_of_nonpos_left hc (by nlinarith only [ha] : -2 * a ≤ 0)
  calc
    _ ≤ ‖u - p‖ ^ 2 + a ^ 2 * (3 * L * ‖u - p‖) ^ 2 -
        2 * a * (L * ‖u - p‖ ^ 2) := by nlinarith only [hpos, hneg]
    _ = (8 / 9 : ℝ) * ‖u - p‖ ^ 2 := by dsimp [a]; field_simp <;> ring

theorem iterate_squared_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y : F) (n : ℕ) :
    ‖iterate J L x y u0 n - primal J L x y‖ ^ 2 ≤
      (8 / 9 : ℝ) ^ n * ‖u0 - primal J L x y‖ ^ 2 := by
  induction n with
  | zero => simp only [iterate, Nat.rec_zero, pow_zero, one_mul, le_refl]
  | succ n ih =>
    change ‖step J L x y (iterate J L x y u0 n) - primal J L x y‖ ^ 2 ≤ _
    calc
      _ ≤ (8 / 9 : ℝ) * ‖iterate J L x y u0 n - primal J L x y‖ ^ 2 :=
        step_squared_contraction J L hL hC2 hLip x _ y
      _ ≤ (8 / 9 : ℝ) * ((8 / 9 : ℝ) ^ n * ‖u0 - primal J L x y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (8 / 9 : ℝ) ^ (n + 1) * ‖u0 - primal J L x y‖ ^ 2 := by rw [pow_succ]; ring

theorem geometric_exponential_bound (n : ℕ) :
    (8 / 9 : ℝ) ^ n ≤ Real.exp (-(n : ℝ) / 9) := by
  have hq : (8 / 9 : ℝ) ≤ Real.exp (-1 / 9) := by
    nlinarith only [Real.add_one_le_exp (-1 / 9)]
  calc
    _ ≤ (Real.exp (-1 / 9)) ^ n := pow_le_pow_left₀ (by norm_num) hq n
    _ = Real.exp (-(n : ℝ) / 9) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem logarithmic_geometric_accuracy (D e : ℝ) (hD : 0 ≤ D) (he : 0 < e) :
    (8 / 9 : ℝ) ^ logBudget D e * D ^ 2 ≤ (e / 3) ^ 2 := by
  let t := 1 + 3 * D / e
  have ht : 0 < t := by dsimp [t]; positivity
  have hceil : 18 * Real.log t ≤ (logBudget D e : ℝ) := Nat.le_ceil _
  have hpow : (8 / 9 : ℝ) ^ logBudget D e ≤ (t ^ 2)⁻¹ := by
    calc
      _ ≤ Real.exp (-(logBudget D e : ℝ) / 9) := geometric_exponential_bound _
      _ ≤ Real.exp (-(2 * Real.log t)) := Real.exp_le_exp.mpr (by linarith only [hceil])
      _ = (t ^ 2)⁻¹ := by
        rw [Real.exp_neg, show 2 * Real.log t = Real.log t + Real.log t by ring,
          Real.exp_add, Real.exp_log ht]
        ring
  have hratio : D / t ≤ e / 3 := by
    apply (div_le_iff₀ ht).mpr
    dsimp [t]
    have he0 : e ≠ 0 := ne_of_gt he
    field_simp
    nlinarith only [he]
  have hsquare : (D / t) ^ 2 ≤ (e / 3) ^ 2 :=
    (sq_le_sq₀ (by positivity : 0 ≤ D / t) (by positivity : 0 ≤ e / 3)).mpr hratio
  calc
    _ ≤ (t ^ 2)⁻¹ * D ^ 2 := mul_le_mul_of_nonneg_right hpow (sq_nonneg D)
    _ = (D / t) ^ 2 := by field_simp
    _ ≤ (e / 3) ^ 2 := hsquare

theorem logBudget_query_bound (D e : ℝ) (hD : 0 ≤ D) (he : 0 < e) :
    (logBudget D e : ℝ) + 1 ≤ 2 + 18 * Real.log (1 + 3 * D / e) := by
  have ht : 1 ≤ 1 + 3 * D / e := by
    have hp : 0 ≤ 3 * D / e := by positivity
    linarith
  have hl : 0 ≤ 18 * Real.log (1 + 3 * D / e) := by
    exact mul_nonneg (by norm_num) (Real.log_nonneg ht)
  have hc := Nat.ceil_lt_add_one hl
  change (logBudget D e : ℝ) < 18 * Real.log (1 + 3 * D / e) + 1 at hc
  linarith


theorem iterate_at_budget_certified
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y : F) (D e : ℝ) (hD : 0 ≤ D) (he : 0 < e)
    (hinit : ‖u0 - primal J L x y‖ ≤ D) :
    ‖iterate J L x y u0 (logBudget D e) - primal J L x y‖ ≤ e / 3 ∧
    ‖OriginalPrimalElimination.residual J L x
      (y, iterate J L x y u0 (logBudget D e))‖ ≤ L * e := by
  let u := iterate J L x y u0 (logBudget D e)
  have hiter := iterate_squared_bound J L hL hC2 hLip x u0 y (logBudget D e)
  have hsq : ‖u - primal J L x y‖ ^ 2 ≤ (e / 3) ^ 2 := by
    calc
      _ ≤ (8 / 9 : ℝ) ^ logBudget D e * ‖u0 - primal J L x y‖ ^ 2 := hiter
      _ ≤ (8 / 9 : ℝ) ^ logBudget D e * D ^ 2 :=
        mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hD).mpr hinit) (by positivity)
      _ ≤ (e / 3) ^ 2 := logarithmic_geometric_accuracy D e hD he
  have hu : ‖u - primal J L x y‖ ≤ e / 3 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ e / 3)).mp hsq
  refine ⟨hu, ?_⟩
  calc
    _ ≤ 3 * L * ‖u - primal J L x y‖ := residual_norm_upper J L hL hC2 hLip x u y
    _ ≤ 3 * L * (e / 3) := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 3 * L)
    _ = L * e := by ring

theorem observed_initial_residual_simulation
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u0 : E) (y : F) (e : ℝ) (he : 0 < e) :
    let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
    let n := logBudget D e
    let u := iterate J L x y u0 n
    ‖OriginalPrimalElimination.residual J L x (y, u)‖ ≤ L * e ∧
    ‖u - primal J L x y‖ ≤ e ∧
    |valueEstimate J L x u y - psi J L x y| ≤ 3 * L / 2 * e ^ 2 ∧
    ‖gradientEstimate J u y - gradient (psi J L x) y‖ ≤ L * e ∧
    ‖schurAt J L u y - fderiv ℝ (gradient (psi J L x)) y‖ ≤ 4 * ρ * e ∧
    (n : ℝ) + 1 ≤ 2 + 18 * Real.log (1 + 3 * D / e) := by
  let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hinit : ‖u0 - primal J L x y‖ ≤ D := observable_residual_distance J L hL hC2 hLip x u0 y
  have hu := iterate_at_budget_certified J L hL hC2 hLip x u0 y D e hD he hinit
  have hdist : ‖iterate J L x y u0 (logBudget D e) - primal J L x y‖ ≤ e :=
    hu.1.trans (by linarith only [he])
  have herr := plug_in_errors_at_tolerance J L ρ hL hρ hC2 hLip hHess x
    (iterate J L x y u0 (logBudget D e)) y e hdist
  exact ⟨hu.2, hdist, herr.1, herr.2.1, herr.2.2, logBudget_query_bound D e hD he⟩


theorem primal_center_lipschitz
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x x' : E) (y : F) :
    ‖primal J L x y - primal J L x' y‖ ≤ 2 * ‖x - x'‖ := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hzero := residual_zero_at_primal J L hL hJ hLip x y
  have hr : OriginalPrimalElimination.residual J L x' (y, primal J L x y) =
      (2 * L) • (x - x') := by
    have heq : OriginalPrimalElimination.residual J L x' (y, primal J L x y) =
        OriginalPrimalElimination.residual J L x (y, primal J L x y) + (2 * L) • (x - x') := by
      dsimp [OriginalPrimalElimination.residual]
      module
    rw [heq, hzero, zero_add]
  have hb := observable_residual_distance J L hL hC2 hLip x' (primal J L x y) y
  rw [hr, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * L)] at hb
  have heq : (2 * L * ‖x - x'‖) / L = 2 * ‖x - x'‖ := by field_simp
  rwa [heq] at hb

theorem warm_initial_residual_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x x' : E) (y y' : F) :
    ‖OriginalPrimalElimination.residual J L x (y, primal J L x' y')‖ / L ≤
      3 * (2 * ‖x' - x‖ + ‖y' - y‖) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hx := primal_center_lipschitz J L hL hC2 hLip x' x y'
  have hy := primal_lipschitz J L hL hJ hLip x y' y
  have htri := dist_triangle (primal J L x' y') (primal J L x y') (primal J L x y)
  simp only [dist_eq_norm] at htri
  have hd : ‖primal J L x' y' - primal J L x y‖ ≤ 2 * ‖x' - x‖ + ‖y' - y‖ :=
    htri.trans (add_le_add hx hy)
  have hr := residual_norm_upper J L hL hC2 hLip x (primal J L x' y') y
  apply (div_le_iff₀ hL).mpr
  have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 3 * L)
  nlinarith only [hr, hm]

end OriginalDualOracleGD
end

section
-- Source component: DualOracleProgram.lean

namespace OriginalDualOracleProgram

open OriginalSaddleImplicit
open OriginalPrimalElimination
open OriginalDualCurvature
open OriginalDualOracleEstimates
open OriginalDualOracleGD

inductive QueryProgram (Z A V : Type*) where
  | pure (value : V)
  | ask (point : Z) (next : A → QueryProgram Z A V)

noncomputable def execute {Z A V : Type*} (oracle : Z → A) : QueryProgram Z A V → V × ℕ
  | .pure v => (v, 0)
  | .ask z next => let r := execute oracle (next (oracle z)); (r.1, r.2 + 1)

structure OracleAnswer (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] where
  value : ℝ
  grad : Z
  hess : Z →L[ℝ] Z

structure QueryState (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  u : E
  answer : OracleAnswer (Joint E F)

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def actualOracle (J : Joint E F → ℝ) (w : Joint E F) : OracleAnswer (Joint E F) :=
  ⟨J w, gradient J w, fderiv ℝ (gradient J) w⟩

noncomputable def actualState (J : Joint E F → ℝ) (y : F) (u : E) : QueryState E F :=
  ⟨u, actualOracle J (JointSliceRegularity.point u y)⟩

noncomputable def answerResidual (L : ℝ) (x : E) (s : QueryState E F) : E :=
  s.answer.grad.fst + (2 * L) • (s.u - x)

noncomputable def nextPoint (L : ℝ) (x : E) (s : QueryState E F) : E :=
  s.u - (1 / (9 * L)) • answerResidual L x s

noncomputable def loop (L : ℝ) (x : E) (y : F) : ℕ → QueryState E F →
    QueryProgram (Joint E F) (OracleAnswer (Joint E F)) (QueryState E F)
  | 0, s => .pure s
  | n + 1, s => .ask (JointSliceRegularity.point (nextPoint L x s) y)
      (fun a => loop L x y n ⟨nextPoint L x s, a⟩)

/-- The initial oracle response is cached for both the initial radius certificate and first step.
Each subsequent query supplies the gradient for the next step and the final plug-in Hessian/value. -/
noncomputable def simulator (L : ℝ) (x : E) (y : F) (u0 : E) (e : ℝ) :
    QueryProgram (Joint E F) (OracleAnswer (Joint E F)) (QueryState E F) :=
  .ask (JointSliceRegularity.point u0 y) (fun a0 =>
    let s0 : QueryState E F := ⟨u0, a0⟩
    loop L x y (logBudget (‖answerResidual L x s0‖ / L) e) s0)

theorem loop_query_count
    (oracle : Joint E F → OracleAnswer (Joint E F)) (L : ℝ) (x : E) (y : F)
    (n : ℕ) (s : QueryState E F) : (execute oracle (loop L x y n s)).2 = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [loop, execute, ih]

theorem iterate_shift (J : Joint E F → ℝ) (L : ℝ) (x u : E) (y : F) (n : ℕ) :
    iterate J L x y u (n + 1) = iterate J L x y (step J L x y u) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step J L x y (iterate J L x y u (n + 1)) =
      step J L x y (iterate J L x y (step J L x y u) n)
    rw [ih]

theorem loop_actual_state
    (J : Joint E F → ℝ) (L : ℝ) (x u : E) (y : F) (n : ℕ) :
    (execute (actualOracle J) (loop L x y n (actualState J y u))).1 =
      actualState J y (iterate J L x y u n) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    change (execute (actualOracle J)
      (loop L x y n (actualState J y (step J L x y u)))).1 = _
    rw [ih, ← iterate_shift]

theorem simulator_actual_execution
    (J : Joint E F → ℝ) (L : ℝ) (x u0 : E) (y : F) (e : ℝ) :
    let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
    let n := logBudget D e
    execute (actualOracle J) (simulator L x y u0 e) =
      (actualState J y (iterate J L x y u0 n), n + 1) := by
  dsimp only [simulator, execute]
  apply Prod.ext
  · exact loop_actual_state J L x u0 y _
  · exact congrArg (fun k : ℕ => k + 1) (loop_query_count (actualOracle J) L x y _ _)

noncomputable def valueOutput (L : ℝ) (x : E) (s : QueryState E F) : ℝ :=
  -(s.answer.value + L * ‖s.u - x‖ ^ 2)

noncomputable def gradientOutput (s : QueryState E F) : F := -s.answer.grad.snd

noncomputable def hessianOutput (L : ℝ) (s : QueryState E F) : F →L[ℝ] F :=
  let X := (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap
  let Y := (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap
  let A := (WithLp.fstL 2 ℝ E F).comp (s.answer.hess.comp X) +
    (2 * L) • ContinuousLinearMap.id ℝ E
  let U := (WithLp.fstL 2 ℝ E F).comp (s.answer.hess.comp Y)
  let V := (WithLp.sndL 2 ℝ E F).comp (s.answer.hess.comp X)
  let W := (WithLp.sndL 2 ℝ E F).comp (s.answer.hess.comp Y);
  -W + V.comp (A.inverse.comp U)

theorem actual_state_outputs
    (J : Joint E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ) (x u : E) (y : F) :
    valueOutput L x (actualState J y u) = valueEstimate J L x u y ∧
    gradientOutput (actualState J y u) = gradientEstimate J u y ∧
    hessianOutput L (actualState J y u) = schurAt J L u y := by
  refine ⟨rfl, ?_, rfl⟩
  change -(gradient J (JointSliceRegularity.point u y)).snd =
    -gradient (JointSliceRegularity.curry J u) y
  rw [JointSliceRegularity.gradient_y_slice_eq_projection J hJ]

/-- The algorithm itself only sees oracle answers. This theorem proves its actual errors,
observable certificate and exact query budget against the original second-order oracle. -/
theorem reduced_dual_oracle_simulation
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u0 : E) (y : F) (e : ℝ) (he : 0 < e) :
    let run := execute (actualOracle J) (simulator L x y u0 e)
    let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
    ‖answerResidual L x run.1‖ ≤ L * e ∧
    ‖run.1.u - primal J L x y‖ ≤ e ∧
    |valueOutput L x run.1 - psi J L x y| ≤ 3 * L / 2 * e ^ 2 ∧
    ‖gradientOutput run.1 - gradient (psi J L x) y‖ ≤ L * e ∧
    ‖hessianOutput L run.1 - fderiv ℝ (gradient (psi J L x)) y‖ ≤ 4 * ρ * e ∧
    (run.2 : ℝ) ≤ 2 + 18 * Real.log (1 + 3 * D / e) := by
  rw [simulator_actual_execution]
  dsimp only
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hout := actual_state_outputs J hJ L x
    (iterate J L x y u0 (logBudget (‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L) e)) y
  rw [hout.1, hout.2.1, hout.2.2]
  simpa only [Nat.cast_add, Nat.cast_one, answerResidual, actualState, actualOracle,
    OriginalPrimalElimination.residual] using
    observed_initial_residual_simulation J L ρ hL hρ hC2 hLip hHess x u0 y e he


theorem arbitrary_accuracy_simulation
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u0 : E) (y : F) (δ : ℝ) (hδ : 0 < δ) :
    let e := min 1 (δ / (1 + 3 * L + 4 * ρ))
    let run := execute (actualOracle J) (simulator L x y u0 e)
    let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
    0 < e ∧
    |valueOutput L x run.1 - psi J L x y| ≤ δ ∧
    ‖gradientOutput run.1 - gradient (psi J L x) y‖ ≤ δ ∧
    ‖hessianOutput L run.1 - fderiv ℝ (gradient (psi J L x)) y‖ ≤ δ ∧
    (run.2 : ℝ) ≤ 2 + 18 * Real.log (1 + 3 * D / e) := by
  let c := 1 + 3 * L + 4 * ρ
  let e := min 1 (δ / c)
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < e := lt_min (by norm_num) (div_pos hδ hc)
  have he1 : e ≤ 1 := min_le_left _ _
  have heδ : e ≤ δ / c := min_le_right _ _
  have hce : c * e ≤ δ := by
    have hh := (le_div_iff₀ hc).mp heδ
    nlinarith only [hh]
  have he2 : e ^ 2 ≤ e := by nlinarith only [he, he1]
  have hv : 3 * L / 2 * e ^ 2 ≤ δ := by
    calc
      _ ≤ 3 * L / 2 * e := mul_le_mul_of_nonneg_left he2 (by positivity)
      _ ≤ c * e := mul_le_mul_of_nonneg_right (by dsimp [c]; linarith only [hL, hρ]) he.le
      _ ≤ δ := hce
  have hg : L * e ≤ δ :=
    (mul_le_mul_of_nonneg_right (by dsimp [c]; linarith only [hL, hρ]) he.le).trans hce
  have hH : 4 * ρ * e ≤ δ :=
    (mul_le_mul_of_nonneg_right (by dsimp [c]; linarith only [hL]) he.le).trans hce
  have hs := reduced_dual_oracle_simulation J L ρ hL hρ hC2 hLip hHess x u0 y e he
  exact ⟨he, hs.2.2.1.trans hv, hs.2.2.2.1.trans hg,
    hs.2.2.2.2.1.trans hH, hs.2.2.2.2.2⟩


theorem dual_oracle_from_standing_joint
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u0 : E) (y : F) :
    (∀ u : E, ∀ e : ℝ, ‖u - primal J L x y‖ ≤ e →
      |valueEstimate J L x u y - psi J L x y| ≤ 3 * L / 2 * e ^ 2 ∧
      ‖gradientEstimate J u y - gradient (psi J L x) y‖ ≤ L * e ∧
      ‖schurAt J L u y - fderiv ℝ (gradient (psi J L x)) y‖ ≤ 4 * ρ * e) ∧
    (∀ δ : ℝ, 0 < δ →
      let e := min 1 (δ / (1 + 3 * L + 4 * ρ))
      let run := execute (actualOracle J) (simulator L x y u0 e)
      let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
      0 < e ∧
      |valueOutput L x run.1 - psi J L x y| ≤ δ ∧
      ‖gradientOutput run.1 - gradient (psi J L x) y‖ ≤ δ ∧
      ‖hessianOutput L run.1 - fderiv ℝ (gradient (psi J L x)) y‖ ≤ δ ∧
      (run.2 : ℝ) ≤ 2 + 18 * Real.log (1 + 3 * D / e)) := by
  exact ⟨fun u e he => plug_in_errors_at_tolerance J L ρ hL hρ hC2 hLip hHess x u y e he,
    arbitrary_accuracy_simulation J L ρ hL hρ hC2 hLip hHess x u0 y⟩

end OriginalDualOracleProgram
end

section
-- Source component: DualResidualQueryBound.lean

namespace OriginalDualResidualQueryBound
open OriginalSaddleImplicit
open OriginalPrimalElimination
open OriginalDualOracleGD
open OriginalDualOracleProgram

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def observedRadius (J : Joint E F → ℝ) (L : ℝ) (x u0 : E) (y : F) : ℝ :=
  ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L

theorem actual_residual_lipschitz_in_dual
    (J : Joint E F → ℝ) (L : ℝ)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y y0 : F) :
    ‖OriginalPrimalElimination.residual J L x (y, u0) - OriginalPrimalElimination.residual J L x (y0, u0)‖ ≤ L * ‖y - y0‖ := by
  have heq : OriginalPrimalElimination.residual J L x (y, u0) - OriginalPrimalElimination.residual J L x (y0, u0) =
      (gradient J (JointSliceRegularity.point u0 y)).fst -
        (gradient J (JointSliceRegularity.point u0 y0)).fst := by
    dsimp [OriginalPrimalElimination.residual]
    abel
  rw [heq]
  calc
    _ ≤ ‖gradient J (JointSliceRegularity.point u0 y) - gradient J (JointSliceRegularity.point u0 y0)‖ :=
      JointSliceRegularity.norm_fst_projection_sub _ _
    _ ≤ L * ‖JointSliceRegularity.point u0 y - JointSliceRegularity.point u0 y0‖ := hLip _ _
    _ = L * ‖y - y0‖ := by rw [JointSliceRegularity.norm_point_sub_same_x]

theorem observed_radius_at_query
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y y0 : F) :
    observedRadius J L x u0 y ≤ observedRadius J L x u0 y0 + ‖y - y0‖ := by
  have hr := actual_residual_lipschitz_in_dual J L hLip x u0 y y0
  have ht := norm_le_norm_sub_add (OriginalPrimalElimination.residual J L x (y, u0)) (OriginalPrimalElimination.residual J L x (y0, u0))
  unfold observedRadius
  apply (div_le_iff₀ hL).mpr
  have hdiv : (‖OriginalPrimalElimination.residual J L x (y0, u0)‖ / L) * L = ‖OriginalPrimalElimination.residual J L x (y0, u0)‖ :=
    div_mul_cancel₀ _ (ne_of_gt hL)
  nlinarith only [hr, ht, hdiv]

theorem observed_radius_difference_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y y0 : F) :
    |observedRadius J L x u0 y - observedRadius J L x u0 y0| ≤ ‖y - y0‖ := by
  have h1 := observed_radius_at_query J L hL hLip x u0 y y0
  have h2 := observed_radius_at_query J L hL hLip x u0 y0 y
  rw [norm_sub_rev y0 y] at h2
  exact abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩

theorem actual_simulator_cost_on_query_ball
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y y0 : F) (B e : ℝ) (he : 0 < e) (hball : ‖y - y0‖ ≤ B) :
    ((execute (actualOracle J) (simulator L x y u0 e)).2 : ℝ) ≤
      2 + 18 * Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / e) := by
  have hobs : 0 ≤ observedRadius J L x u0 y := by unfold observedRadius; positivity
  have hquery : observedRadius J L x u0 y ≤ observedRadius J L x u0 y0 + B :=
    (observed_radius_at_query J L hL hLip x u0 y y0).trans (add_le_add le_rfl hball)
  have hc := logBudget_query_bound (observedRadius J L x u0 y) e hobs he
  rw [simulator_actual_execution]
  simp only [Nat.cast_add, Nat.cast_one]
  apply hc.trans
  have hpositive : 0 < 1 + 3 * observedRadius J L x u0 y / e := by positivity
  have hlog : Real.log (1 + 3 * observedRadius J L x u0 y / e) ≤
      Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / e) := Real.log_le_log hpositive
    (by have hm := mul_le_mul_of_nonneg_left hquery (by norm_num : (0 : ℝ) ≤ 3)
        have hd := div_le_div_of_nonneg_right hm he.le
        linarith only [hd])
  nlinarith only [hlog]

end OriginalDualResidualQueryBound
end

section
-- Source component: Upper02DependencyExtract01.lean

namespace CertifiedATS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem gradient_derivative_selfadjoint
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (J : Z → ℝ) (hC2 : ContDiff ℝ 2 J) (w : Z) :
    (fderiv ℝ (gradient J) w).adjoint = fderiv ℝ (gradient J) w := by
  have hfd := ((hC2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) w).hasFDerivAt
  have hgrad : HasFDerivAt (gradient J)
      ((InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ J) w)) w := by
    convert! (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp
      w hfd using 1 <;> rfl
  have hs : IsSymmSndFDerivAt ℝ J w := hC2.contDiffAt.isSymmSndFDerivAt (by simp)
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro a b
  rw [hgrad.fderiv]
  change inner ℝ ((InnerProductSpace.toDual ℝ Z).symm
      (fderiv ℝ (fderiv ℝ J) w a)) b =
    inner ℝ a ((InnerProductSpace.toDual ℝ Z).symm (fderiv ℝ (fderiv ℝ J) w b))
  calc
    inner ℝ ((InnerProductSpace.toDual ℝ Z).symm
        (fderiv ℝ (fderiv ℝ J) w a)) b = fderiv ℝ (fderiv ℝ J) w a b :=
      InnerProductSpace.toDual_symm_apply
    _ = fderiv ℝ (fderiv ℝ J) w b a := hs a b
    _ = inner ℝ ((InnerProductSpace.toDual ℝ Z).symm
        (fderiv ℝ (fderiv ℝ J) w b)) a := InnerProductSpace.toDual_symm_apply.symm
    _ = inner ℝ a ((InnerProductSpace.toDual ℝ Z).symm
        (fderiv ℝ (fderiv ℝ J) w b)) := real_inner_comm _ _


theorem convex_of_global_support
    (g : E → ℝ) (v : E → E)
    (hsupport : ∀ x y : E, g x + inner ℝ (v x) (y - x) ≤ g y) :
    ConvexOn ℝ (Set.univ : Set E) g := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hzero : a • (x - z) + b • (y - z) = 0 := by
    calc
      a • (x - z) + b • (y - z) = a • x + b • y - (a + b) • z := by
        simp only [smul_sub, add_smul]
        abel
      _ = 0 := by rw [hab, one_smul]; exact sub_self z
  have hi := congrArg (fun w : E => inner ℝ (v z) w) hzero
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at hi
  have h1 := mul_le_mul_of_nonneg_left (hsupport z x) ha
  have h2 := mul_le_mul_of_nonneg_left (hsupport z y) hb
  change g z ≤ a * g x + b * g y
  calc
    g z = (a + b) * g z := by rw [hab, one_mul]
    _ = a * (g z + inner ℝ (v z) (x - z)) +
        b * (g z + inner ℝ (v z) (y - z)) := by nlinarith only [hi]
    _ ≤ a * g x + b * g y := add_le_add h1 h2


theorem gradient_differentiable (F : E → ℝ) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (gradient F) := by
  have hder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have heq : gradient F = fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F y) := rfl
  rw [heq]
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hder).differentiable (by norm_num)


noncomputable def sympart (H : E →L[ℝ] E) : E →L[ℝ] E := (1 / 2 : ℝ) • (H + H.adjoint)

noncomputable def model (v : E) (H : E →L[ℝ] E) (Mbar lam : ℝ) (d : E) : ℝ :=
  inner ℝ v d + (1 / 2 : ℝ) * inner ℝ (H d) d +
    Mbar / 6 * ‖d‖ ^ 3 + 1 / (2 * lam) * ‖d‖ ^ 2

noncomputable def trueVector (v : E) (H : E →L[ℝ] E) (Mbar : ℝ) (d : E) : E :=
  v + H d + (Mbar / 2 * ‖d‖) • d

theorem sympart_selfadjoint (H : E →L[ℝ] E) : (sympart H).adjoint = sympart H := by
  simp [sympart, map_smul, map_add, add_comm]

theorem sympart_same_quadratic (H : E →L[ℝ] E) (d : E) :
    inner ℝ (sympart H d) d = inner ℝ (H d) d := by
  simp only [sympart, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    real_inner_smul_left, inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_comm d (H d)]
  ring

theorem sympart_error_bound (H K : E →L[ℝ] E) (hK : K.adjoint = K) :
    ‖sympart H - K‖ ≤ ‖H - K‖ := by
  have he : sympart H - K = (1 / 2 : ℝ) • ((H - K) + (H - K).adjoint) := by
    simp only [sympart, map_sub, hK]
    module
  rw [he, norm_smul]
  have ht := norm_add_le (H - K) (H - K).adjoint
  rw [ContinuousLinearMap.adjoint.norm_map] at ht
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith only [ht]

theorem actual_hessian_coercive (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (mu : ℝ) (hsc : StrongConvexOn (Set.univ : Set E) mu g) (z d : E) :
    mu * ‖d‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient g) z d) d := by
  exact OriginalCoerciveOperator.derivative_coercive_of_strong_monotonicity (gradient g) mu
    (PacketCore.gradient_strong_monotone g mu hsc (hC2.differentiable (by norm_num)))
    z (fderiv ℝ (gradient g) z) (gradient_differentiable g hC2 z).hasFDerivAt d

theorem approximate_hessian_coercive (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (mu : ℝ) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z : E) (H : E →L[ℝ] E) (deltaH : ℝ)
    (herr : ‖H - fderiv ℝ (gradient g) z‖ ≤ deltaH) (hsmall : deltaH ≤ mu / 4) (d : E) :
    (3 * mu / 4) * ‖d‖ ^ 2 ≤ inner ℝ (sympart H d) d := by
  have hbase := actual_hessian_coercive g hC2 mu hsc z d
  have he := le_trans (sympart_error_bound H (fderiv ℝ (gradient g) z)
    (gradient_derivative_selfadjoint g hC2 z)) herr
  have hnorm : ‖(sympart H - fderiv ℝ (gradient g) z) d‖ ≤ deltaH * ‖d‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ d)
      (mul_le_mul_of_nonneg_right he (norm_nonneg d))
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm ((sympart H - fderiv ℝ (gradient g) z) d) d)
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left] at hi
  simp only [ContinuousLinearMap.sub_apply] at hnorm
  have hm := mul_le_mul_of_nonneg_right hnorm (norm_nonneg d)
  have hd := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖d‖)
  nlinarith only [hi, hm, hbase, hd]

theorem add_hasGradientAt {f h : E → ℝ} {u v x : E}
    (hf : HasGradientAt f u x) (hh : HasGradientAt h v x) :
    HasGradientAt (fun y => f y + h y) (u + v) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  convert! hf.add hh using 1
  ext d
  simp only [InnerProductSpace.toDual_apply_apply, inner_add_left, ContinuousLinearMap.add_apply]

theorem mul_hasGradientAt {f : E → ℝ} {v x : E} (hf : HasGradientAt f v x) (a : ℝ) :
    HasGradientAt (fun y => a * f y) (a • v) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  convert! hf.const_mul a using 1
  ext d
  simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem linear_hasGradientAt (v x : E) : HasGradientAt (fun y => inner ℝ v y) v x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (InnerProductSpace.toDual ℝ E v).hasFDerivAt

theorem quadratic_hasGradientAt (H : E →L[ℝ] E) (x : E) :
    HasGradientAt (fun d => (1 / 2 : ℝ) * inner ℝ (H d) d) (sympart H x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := ((H.hasFDerivAt (x := x)).inner ℝ (hasFDerivAt_id x)).const_mul (1 / 2 : ℝ)
  convert! hh using 1
  ext d
  simp only [sympart, InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, real_inner_smul_left, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, id_eq]
  rw [real_inner_comm (H d) x]
  ring

theorem cube_hasGradientAt (x : E) :
    HasGradientAt (fun d : E => ‖d‖ ^ 3) ((3 * ‖x‖) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := hasFDerivAt_norm_rpow x (p := (3 : ℝ)) (by norm_num)
  have he : (fun d : E => ‖d‖ ^ (3 : ℝ)) = (fun d : E => ‖d‖ ^ (3 : ℕ)) := by
    funext d
    exact Real.rpow_natCast _ 3
  rw [he] at hh
  convert! hh using 1
  ext d
  norm_num [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, innerSL_apply_apply]

theorem square_hasGradientAt (x : E) :
    HasGradientAt (fun d : E => ‖d‖ ^ 2) ((2 : ℝ) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! (hasFDerivAt_id x).norm_sq using 1
  ext d
  simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left, two_smul,
    inner_add_left, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, id_eq]

theorem model_hasGradientAt (v : E) (H : E →L[ℝ] E) (Mbar lam : ℝ) (d : E) :
    HasGradientAt (model v H Mbar lam)
      (v + sympart H d + (Mbar / 2 * ‖d‖) • d + lam⁻¹ • d) d := by
  have hh := add_hasGradientAt
    (add_hasGradientAt (add_hasGradientAt (linear_hasGradientAt v d) (quadratic_hasGradientAt H d))
      (mul_hasGradientAt (cube_hasGradientAt d) (Mbar / 6)))
    (mul_hasGradientAt (square_hasGradientAt d) (1 / (2 * lam)))
  convert! hh using 1 <;> module

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def halvingCount (a tau : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (max 1 (a / tau)))

theorem halving_precision (a tau : ℝ) (htau : 0 < tau) :
    a / (2 : ℝ) ^ (halvingCount a tau) ≤ tau := by
  have hm : 0 < max 1 (a / tau) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hn : Real.logb 2 (max 1 (a / tau)) ≤ (halvingCount a tau : ℝ) := Nat.le_ceil _
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hn
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hm,
    Real.rpow_natCast] at hp
  have hh := le_trans (le_max_right 1 (a / tau)) hp
  have hmul := (div_le_iff₀ htau).mp hh
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  nlinarith only [hmul]

theorem center_thresholds_cover (v : E) (delta rhoStop : ℝ)
    (hrho : 0 < rhoStop) (hsmall : delta ≤ rhoStop / 8) :
    ‖v‖ + delta ≤ rhoStop ∨ rhoStop / 2 ≤ ‖v‖ - delta := by
  by_cases hs : ‖v‖ + delta ≤ rhoStop
  · exact Or.inl hs
  · exact Or.inr (by linarith only [lt_of_not_ge hs, hsmall, hrho])

theorem center_stop_certifies (v G : E) (delta rhoStop : ℝ)
    (herr : ‖v - G‖ ≤ delta) (hstop : ‖v‖ + delta ≤ rhoStop) : ‖G‖ ≤ rhoStop := by
  have ht := norm_le_norm_sub_add G v
  rw [norm_sub_rev G v] at ht
  linarith only [ht, herr, hstop]

theorem center_away_certifies (v G : E) (delta rhoStop : ℝ)
    (herr : ‖v - G‖ ≤ delta) (haway : rhoStop / 2 ≤ ‖v‖ - delta) : rhoStop / 2 ≤ ‖G‖ := by
  have ht := norm_le_norm_sub_add v G
  linarith only [ht, herr, haway]

theorem center_geometric_termination (G : E) (v : ℕ → E) (error0 rhoStop : ℝ)
    (hrho : 0 < rhoStop)
    (herr : ∀ n : ℕ, ‖v n - G‖ ≤ error0 / (2 : ℝ) ^ n) :
    let n := halvingCount error0 (rhoStop / 8)
    (‖v n‖ + error0 / (2 : ℝ) ^ n ≤ rhoStop ∧ ‖G‖ ≤ rhoStop) ∨
    (rhoStop / 2 ≤ ‖v n‖ - error0 / (2 : ℝ) ^ n ∧ rhoStop / 2 ≤ ‖G‖) := by
  dsimp only
  have hs := halving_precision error0 (rhoStop / 8) (by positivity)
  rcases center_thresholds_cover (v (halvingCount error0 (rhoStop / 8)))
      (error0 / (2 : ℝ) ^ (halvingCount error0 (rhoStop / 8))) rhoStop hrho hs with hstop | haway
  · exact Or.inl ⟨hstop, center_stop_certifies _ G _ rhoStop (herr _) hstop⟩
  · exact Or.inr ⟨haway, center_away_certifies _ G _ rhoStop (herr _) haway⟩

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem quadratic_remainder (H : E →L[ℝ] E) (x y : E) :
    (1 / 2 : ℝ) * inner ℝ (H y) y - (1 / 2 : ℝ) * inner ℝ (H x) x -
      inner ℝ (sympart H x) (y - x) = (1 / 2 : ℝ) * inner ℝ (H (y - x)) (y - x) := by
  simp only [sympart, map_sub, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    real_inner_smul_left, inner_add_left, inner_sub_left, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_comm x (H y), real_inner_comm x (H x)]
  ring

theorem quadratic_strongConvex (H : E →L[ℝ] E) (m : ℝ)
    (hcoer : ∀ d : E, m * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    StrongConvexOn (Set.univ : Set E) m (fun d => (1 / 2 : ℝ) * inner ℝ (H d) d) := by
  apply strongConvexOn_iff_convex.mpr
  apply convex_of_global_support _ (fun d => sympart H d - m • d)
  intro x y
  have hr := quadratic_remainder H x y
  have hc := hcoer (y - x)
  simp only [inner_sub_left, real_inner_smul_left, inner_sub_right]
  rw [norm_sub_sq_real] at hc
  have hxy : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
  rw [hxy] at hc
  simp only [inner_sub_right] at hc
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at hr ⊢
  nlinarith only [hr, hc]

theorem model_strongConvex (v : E) (H : E →L[ℝ] E) (Mbar lam m : ℝ)
    (hM : 0 ≤ Mbar) (hlam : 0 < lam)
    (hcoer : ∀ d : E, m * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    StrongConvexOn (Set.univ : Set E) m (model v H Mbar lam) := by
  have hlin : ConvexOn ℝ (Set.univ : Set E) (fun d => inner ℝ v d) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [inner_add_right, inner_smul_right, smul_eq_mul, le_refl]
  have hcub : ConvexOn ℝ (Set.univ : Set E) (fun d => Mbar / 6 * ‖d‖ ^ 3) := by
    simpa only [Pi.pow_apply, smul_eq_mul] using
      ConvexOn.smul (by positivity : 0 ≤ Mbar / 6)
        (convexOn_univ_norm.pow (fun d _ => norm_nonneg d) 3)
  have hprox : ConvexOn ℝ (Set.univ : Set E) (fun d => 1 / (2 * lam) * ‖d‖ ^ 2) := by
    simpa only [Pi.pow_apply, smul_eq_mul] using
      ConvexOn.smul (by positivity : 0 ≤ 1 / (2 * lam))
        (convexOn_univ_norm.pow (fun d _ => norm_nonneg d) 2)
  have hq := strongConvexOn_iff_convex.mp (quadratic_strongConvex H m hcoer)
  have hh := ((hq.add hlin).add hcub).add hprox
  apply strongConvexOn_iff_convex.mpr
  convert! hh using 1
  funext d
  simp only [Pi.add_apply, model]
  ring

theorem exists_model_minimum (v : E) (H : E →L[ℝ] E) (Mbar lam m : ℝ)
    (hM : 0 ≤ Mbar) (hlam : 0 < lam) (hm : 0 < m)
    (hcoer : ∀ d : E, m * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    ∃ d : E, ∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w := by
  have hd : Differentiable ℝ (model v H Mbar lam) := fun d =>
    (model_hasGradientAt v H Mbar lam d).differentiableAt
  obtain ⟨d, hdmin⟩ := PacketCore.exists_inner_maximizer_finiteDimensional
    (model v H Mbar lam) m 0 0 0 0 hm
    (by simpa using model_strongConvex v H Mbar lam m hM hlam hcoer) hd (0 : E)
  refine ⟨d, ?_⟩
  intro w
  simpa [PacketCore.saddleValue] using hdmin w

theorem model_minimum_first_order (v : E) (H : E →L[ℝ] E) (Mbar lam : ℝ) (d : E)
    (hmin : ∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) :
    v + sympart H d + (Mbar / 2 * ‖d‖) • d + lam⁻¹ • d = 0 := by
  have hz := PacketCore.gradient_eq_zero_at_global_min (model v H Mbar lam) d hmin
  rw [(model_hasGradientAt v H Mbar lam d).gradient] at hz
  exact hz

theorem residual_from_actual_minimum (G v : E) (K H : E →L[ℝ] E)
    (Mbar lam deltaG deltaH : ℝ) (hlam : 0 < lam) (hK : K.adjoint = K)
    (hgrad : ‖v - G‖ ≤ deltaG) (hhess : ‖H - K‖ ≤ deltaH)
    (d : E) (hmin : ∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) :
    ‖lam • trueVector G K Mbar d + d‖ ≤ lam * (deltaG + deltaH * ‖d‖) := by
  have hfoc := model_minimum_first_order v H Mbar lam d hmin
  have hs : lam • (v + sympart H d + (Mbar / 2 * ‖d‖) • d) + d = 0 := by
    calc
      _ = lam • (v + sympart H d + (Mbar / 2 * ‖d‖) • d + lam⁻¹ • d) := by
        simp only [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hlam), one_smul]
      _ = 0 := by rw [hfoc, smul_zero]
  have he : lam • trueVector G K Mbar d + d =
      lam • (G - v + (K - sympart H) d) := by
    calc
      _ = lam • (G - v + (K - sympart H) d) +
          (lam • (v + sympart H d + (Mbar / 2 * ‖d‖) • d) + d) := by
            simp only [trueVector, ContinuousLinearMap.sub_apply]
            module
      _ = _ := by rw [hs, add_zero]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  apply mul_le_mul_of_nonneg_left _ hlam.le
  have hsym := le_trans (sympart_error_bound H K hK) hhess
  have hmap : ‖(K - sympart H) d‖ ≤ deltaH * ‖d‖ := by
    apply le_trans (ContinuousLinearMap.le_opNorm _ d)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg d)
    simpa only [norm_sub_rev K (sympart H)] using hsym
  have hg : ‖G - v‖ ≤ deltaG := by simpa only [norm_sub_rev G v] using hgrad
  exact le_trans (norm_add_le _ _) (add_le_add hg hmap)

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def stepFloor (rhoStop A Mbar : ℝ) : ℝ :=
  min 1 (rhoStop / (8 * (A + Mbar / 2)))

theorem stepFloor_positive (rhoStop A Mbar : ℝ)
    (hrho : 0 < rhoStop) (hA : 0 < A) (hM : 0 ≤ Mbar) : 0 < stepFloor rhoStop A Mbar := by
  unfold stepFloor
  exact lt_min zero_lt_one (by positivity)

theorem minimum_gradient_norm_bound (v : E) (H : E →L[ℝ] E) (Mbar lam B : ℝ)
    (hM : 0 ≤ Mbar) (hlam : 0 < lam) (hB : ‖sympart H‖ ≤ B)
    (d : E) (hmin : ∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) :
    ‖v‖ ≤ (B + lam⁻¹) * ‖d‖ + (Mbar / 2) * ‖d‖ ^ 2 := by
  have hfoc := model_minimum_first_order v H Mbar lam d hmin
  have he : v = -(sympart H d + (Mbar / 2 * ‖d‖) • d + lam⁻¹ • d) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc] using hfoc
  rw [he, norm_neg]
  have h1 := norm_add_le (sympart H d) ((Mbar / 2 * ‖d‖) • d)
  have h2 := norm_add_le (sympart H d + (Mbar / 2 * ‖d‖) • d) (lam⁻¹ • d)
  have hQ : ‖sympart H d‖ ≤ B * ‖d‖ := le_trans (ContinuousLinearMap.le_opNorm _ _)
    (mul_le_mul_of_nonneg_right hB (norm_nonneg d))
  have hC : ‖(Mbar / 2 * ‖d‖) • d‖ = (Mbar / 2) * ‖d‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  have hP : ‖lam⁻¹ • d‖ = lam⁻¹ * ‖d‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
  rw [hC] at h1
  rw [hP] at h2
  nlinarith only [h1, h2, hQ]

theorem approximate_minimum_step_lower (v : E) (H : E →L[ℝ] E)
    (Mbar lam B rhoStop : ℝ)
    (hM : 0 ≤ Mbar) (hlam : 0 < lam) (hB : ‖sympart H‖ ≤ B)
    (hA : 0 < B + lam⁻¹) (hrho : 0 < rhoStop) (haway : rhoStop / 4 ≤ ‖v‖)
    (d : E) (hmin : ∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) :
    stepFloor rhoStop (B + lam⁻¹) Mbar ≤ ‖d‖ := by
  have hb := minimum_gradient_norm_bound v H Mbar lam B hM hlam hB d hmin
  by_contra hfail
  have hd : ‖d‖ < stepFloor rhoStop (B + lam⁻¹) Mbar := lt_of_not_ge hfail
  have hd1 : ‖d‖ ≤ 1 := le_trans hd.le (min_le_left _ _)
  have hsq : ‖d‖ ^ 2 ≤ ‖d‖ := by nlinarith only [norm_nonneg d, hd1]
  have hC : 0 < B + lam⁻¹ + Mbar / 2 := by linarith only [hA, hM]
  have hdf : ‖d‖ < rhoStop / (8 * (B + lam⁻¹ + Mbar / 2)) :=
    lt_of_lt_of_le hd (min_le_right _ _)
  have hh := (lt_div_iff₀ (by positivity : 0 < 8 * (B + lam⁻¹ + Mbar / 2))).mp hdf
  have hsqM := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ Mbar / 2)
  nlinarith only [hb, haway, hh, hsqM, hrho]

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def refinementTolerance (mu Lg Mbar lam sigma rhoStop : ℝ) : ℝ :=
  let ell := stepFloor rhoStop (Lg + mu / 4 + lam⁻¹) Mbar
  min (rhoStop / 8) (min (mu / 4) (min (sigma * ell / (2 * lam)) (sigma / (2 * lam))))

theorem refinementTolerance_bounds (mu Lg Mbar lam sigma rhoStop : ℝ) :
    refinementTolerance mu Lg Mbar lam sigma rhoStop ≤ rhoStop / 8 ∧
    refinementTolerance mu Lg Mbar lam sigma rhoStop ≤ mu / 4 ∧
    refinementTolerance mu Lg Mbar lam sigma rhoStop ≤
      sigma * stepFloor rhoStop (Lg + mu / 4 + lam⁻¹) Mbar / (2 * lam) ∧
    refinementTolerance mu Lg Mbar lam sigma rhoStop ≤ sigma / (2 * lam) := by
  dsimp only [refinementTolerance]
  exact ⟨min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)),
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))⟩

theorem refinementTolerance_positive (mu Lg Mbar lam sigma rhoStop : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ Mbar) (hlam : 0 < lam)
    (hsigma : 0 < sigma) (hrho : 0 < rhoStop) :
    0 < refinementTolerance mu Lg Mbar lam sigma rhoStop := by
  have hell : 0 < stepFloor rhoStop (Lg + mu / 4 + lam⁻¹) Mbar :=
    stepFloor_positive rhoStop _ Mbar hrho (by positivity) hM
  unfold refinementTolerance
  positivity

theorem hessian_norm_from_gradient_lipschitz (g : E → ℝ) (Lg : ℝ) (hLg : 0 ≤ Lg)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖) (z : E) :
    ‖fderiv ℝ (gradient g) z‖ ≤ Lg := by
  let C : NNReal := ⟨Lg, hLg⟩
  have hh : LipschitzWith C (gradient g) := lipschitzWith_iff_norm_sub_le.mpr hlip
  exact norm_fderiv_le_of_lipschitz ℝ hh

theorem halving_precision_of_ge (a tau : ℝ) (ha : 0 ≤ a) (htau : 0 < tau)
    (n : ℕ) (hn : halvingCount a tau ≤ n) : a / (2 : ℝ) ^ n ≤ tau := by
  have hh : a / (2 : ℝ) ^ n ≤ a / (2 : ℝ) ^ (halvingCount a tau) :=
    div_le_div_of_nonneg_left ha (pow_pos (by norm_num) _)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn)
  exact le_trans hh (halving_precision a tau htau)

theorem model_acceptance_at_accuracy
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu Lg Mbar lam sigma rhoStop : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ Mbar) (hlam : 0 < lam)
    (hsigma : 0 < sigma) (hrho : 0 < rhoStop)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (z v : E) (H : E →L[ℝ] E) (eta : ℝ)
    (hgerr : ‖v - gradient g z‖ ≤ eta)
    (hHerr : ‖H - fderiv ℝ (gradient g) z‖ ≤ eta)
    (hsmall : eta ≤ refinementTolerance mu Lg Mbar lam sigma rhoStop)
    (haway : rhoStop / 2 ≤ ‖gradient g z‖) :
    ∃ d : E, (∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) ∧
      stepFloor rhoStop (Lg + mu / 4 + lam⁻¹) Mbar ≤ ‖d‖ ∧
      lam * (eta + eta * ‖d‖) ≤ sigma * ‖d‖ ∧
      ‖lam • trueVector (gradient g z) (fderiv ℝ (gradient g) z) Mbar d + d‖ ≤ sigma * ‖d‖ := by
  have hb := refinementTolerance_bounds mu Lg Mbar lam sigma rhoStop
  have he1 := le_trans hsmall hb.1
  have he2 := le_trans hsmall hb.2.1
  have he3 := le_trans hsmall hb.2.2.1
  have he4 := le_trans hsmall hb.2.2.2
  have hcoer : ∀ d : E, (3 * mu / 4) * ‖d‖ ^ 2 ≤ inner ℝ (H d) d := by
    intro d
    simpa only [sympart_same_quadratic] using
      approximate_hessian_coercive g hC2 mu hsc z H eta hHerr he2 d
  obtain ⟨d, hd⟩ := exists_model_minimum v H Mbar lam (3 * mu / 4) hM hlam (by positivity) hcoer
  have hK := hessian_norm_from_gradient_lipschitz g Lg hLg hlip z
  have hsym := le_trans (sympart_error_bound H (fderiv ℝ (gradient g) z)
    (gradient_derivative_selfadjoint g hC2 z)) hHerr
  have hHnorm : ‖sympart H‖ ≤ Lg + mu / 4 := by
    have ht := norm_le_norm_sub_add (sympart H) (fderiv ℝ (gradient g) z)
    linarith only [ht, hsym, hK, he2]
  have hv : rhoStop / 4 ≤ ‖v‖ := by
    have ht := norm_le_norm_sub_add (gradient g z) v
    rw [norm_sub_rev (gradient g z) v] at ht
    linarith only [ht, hgerr, haway, he1, hrho]
  have hstep := approximate_minimum_step_lower v H Mbar lam (Lg + mu / 4) rhoStop
    hM hlam hHnorm (by positivity) hrho hv d hd
  have hc : lam * (eta + eta * ‖d‖) ≤ sigma * ‖d‖ := by
    have hp1 := (le_div_iff₀ (by positivity : 0 < 2 * lam)).mp he3
    have hp2 := (le_div_iff₀ (by positivity : 0 < 2 * lam)).mp he4
    have hmul := mul_le_mul_of_nonneg_right hp2 (norm_nonneg d)
    have hstepmul := mul_le_mul_of_nonneg_left hstep hsigma.le
    nlinarith only [hp1, hmul, hstepmul]
  refine ⟨d, hd, hstep, hc, ?_⟩
  exact le_trans (residual_from_actual_minimum (gradient g z) v (fderiv ℝ (gradient g) z) H
    Mbar lam eta eta hlam (gradient_derivative_selfadjoint g hC2 z) hgerr hHerr d hd) hc

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem certified_taylor_subroutine_all_items
    (g : E → ℝ) (mu Lg M Mbar lam sigma rhoStop error0 : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hMbar : M ≤ Mbar)
    (hlam : 0 < lam) (hsigma : 0 < sigma) (hrho : 0 < rhoStop) (herror0 : 0 ≤ error0)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (hHlip : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z : E) (vseq : ℕ → E) (Hseq : ℕ → E →L[ℝ] E)
    (hgerr : ∀ n : ℕ, ‖vseq n - gradient g z‖ ≤ error0 / (2 : ℝ) ^ n)
    (hHerr : ∀ n : ℕ, ‖Hseq n - fderiv ℝ (gradient g) z‖ ≤ error0 / (2 : ℝ) ^ n) :
    (∀ (v : E) (H : E →L[ℝ] E) (deltaG deltaH : ℝ) (d : E),
      ‖v - gradient g z‖ ≤ deltaG →
      ‖H - fderiv ℝ (gradient g) z‖ ≤ deltaH → deltaH ≤ mu / 4 →
      (∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) →
      lam * (deltaG + deltaH * ‖d‖) ≤ sigma * ‖d‖ →
      ‖lam • trueVector (gradient g z) (fderiv ℝ (gradient g) z) Mbar d + d‖ ≤ sigma * ‖d‖) ∧
    let nCenter := halvingCount error0 (rhoStop / 8)
    let nAccept := nCenter + halvingCount error0 (refinementTolerance mu Lg Mbar lam sigma rhoStop)
    (‖vseq nCenter‖ + error0 / (2 : ℝ) ^ nCenter ≤ rhoStop ∧ ‖gradient g z‖ ≤ rhoStop) ∨
    (rhoStop / 2 ≤ ‖vseq nCenter‖ - error0 / (2 : ℝ) ^ nCenter ∧
      rhoStop / 2 ≤ ‖gradient g z‖ ∧
      ∃ d : E,
        (∀ w : E, model (vseq nAccept) (Hseq nAccept) Mbar lam d ≤
          model (vseq nAccept) (Hseq nAccept) Mbar lam w) ∧
        stepFloor rhoStop (Lg + mu / 4 + lam⁻¹) Mbar ≤ ‖d‖ ∧
        lam * (error0 / (2 : ℝ) ^ nAccept + error0 / (2 : ℝ) ^ nAccept * ‖d‖) ≤ sigma * ‖d‖ ∧
        ‖lam • trueVector (gradient g z) (fderiv ℝ (gradient g) z) Mbar d + d‖ ≤ sigma * ‖d‖) := by
  have hMnonneg : 0 ≤ Mbar := le_trans hM hMbar
  constructor
  · intro v H deltaG deltaH d hv hH hsmall hd hcert
    exact le_trans (residual_from_actual_minimum (gradient g z) v (fderiv ℝ (gradient g) z) H
      Mbar lam deltaG deltaH hlam (gradient_derivative_selfadjoint g hC2 z) hv hH d hd) hcert
  · dsimp only
    rcases center_geometric_termination (gradient g z) vseq error0 rhoStop hrho hgerr with hstop | haway
    · exact Or.inl hstop
    · refine Or.inr ⟨haway.1, haway.2, ?_⟩
      have htau := refinementTolerance_positive mu Lg Mbar lam sigma rhoStop hmu hLg hMnonneg hlam hsigma hrho
      let n := halvingCount error0 (rhoStop / 8) +
        halvingCount error0 (refinementTolerance mu Lg Mbar lam sigma rhoStop)
      have hn : halvingCount error0 (refinementTolerance mu Lg Mbar lam sigma rhoStop) ≤ n := by
        dsimp only [n]
        omega
      have he := halving_precision_of_ge error0 (refinementTolerance mu Lg Mbar lam sigma rhoStop)
        herror0 htau n hn
      exact model_acceptance_at_accuracy g hC2 mu Lg Mbar lam sigma rhoStop
        hmu hLg hMnonneg hlam hsigma hrho hsc hlip z (vseq n) (Hseq n)
        (error0 / (2 : ℝ) ^ n) (hgerr n) (hHerr n) he haway.2

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def trueTaylorProx (g : E → ℝ) (z : E) (Mbar lam : ℝ) : E → ℝ :=
  model (gradient g z) (fderiv ℝ (gradient g) z) Mbar lam

theorem sympart_eq_of_selfadjoint (K : E →L[ℝ] E) (hK : K.adjoint = K) : sympart K = K := by
  unfold sympart
  rw [hK]
  module

theorem trueTaylorProx_hasGradientAt (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (z d : E) (Mbar lam : ℝ) :
    HasGradientAt (trueTaylorProx g z Mbar lam)
      (trueVector (gradient g z) (fderiv ℝ (gradient g) z) Mbar d + lam⁻¹ • d) d := by
  have hh := model_hasGradientAt (gradient g z) (fderiv ℝ (gradient g) z) Mbar lam d
  rw [sympart_eq_of_selfadjoint _ (gradient_derivative_selfadjoint g hC2 z)] at hh
  exact hh

theorem trueTaylorProx_exists_minimum (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (mu Mbar lam : ℝ) (hmu : 0 < mu) (hM : 0 ≤ Mbar) (hlam : 0 < lam)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g) (z : E) :
    ∃ d : E, ∀ w : E, trueTaylorProx g z Mbar lam d ≤ trueTaylorProx g z Mbar lam w := by
  exact exists_model_minimum (gradient g z) (fderiv ℝ (gradient g) z) Mbar lam mu hM hlam hmu
    (actual_hessian_coercive g hC2 mu hsc z)

end CertifiedATS
end

section
-- Source component: CoupledBetaAlgebra.lean

namespace OriginalCoupledBetaAlgebra

noncomputable def lambda (A b : ℝ) : ℝ := A * b ^ 2 / (1 - b)
noncomputable def weight (A b : ℝ) : ℝ := A * b / (1 - b)

noncomputable def center {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x y : E) (b : ℝ) : E := (1 - b) • y + b • x

theorem coupled_weights (A b : ℝ) (hA : 0 < A) (hb : 0 < b) (hb1 : b < 1) :
    0 < lambda A b ∧ 0 < weight A b ∧
    weight A b ^ 2 = lambda A b * (A + weight A b) ∧
    A / (A + weight A b) = 1 - b ∧
    weight A b / (A + weight A b) = b := by
  have hden : 0 < 1 - b := sub_pos.mpr hb1
  have htotal : A + weight A b = A / (1 - b) := by
    dsimp [weight]
    field_simp <;> ring
  refine ⟨by dsimp [lambda]; positivity, by dsimp [weight]; positivity, ?_, ?_, ?_⟩
  · rw [htotal]
    dsimp [lambda, weight]
    field_simp <;> ring
  · rw [htotal]
    field_simp
  · rw [htotal]
    dsimp [weight]
    field_simp

theorem coupled_square_root_formula (A b : ℝ) (hA : 0 < A) (hb : 0 < b) (hb1 : b < 1) :
    weight A b = (lambda A b + Real.sqrt (lambda A b ^ 2 + 4 * lambda A b * A)) / 2 := by
  have hw := coupled_weights A b hA hb hb1
  have hrel : lambda A b = b * weight A b := by dsimp [lambda, weight]; ring
  have htwo : 0 < 2 * weight A b - lambda A b := by
    rw [hrel]
    nlinarith only [hw.2.1, hb1]
  have hs : (2 * weight A b - lambda A b) ^ 2 = lambda A b ^ 2 + 4 * lambda A b * A := by
    nlinarith only [hw.2.2.1]
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_pos htwo]
  ring

theorem coupled_center {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A b : ℝ) (hA : 0 < A) (hb : 0 < b) (hb1 : b < 1) (x y : E) :
    (A / (A + weight A b)) • y + (weight A b / (A + weight A b)) • x = center x y b := by
  have hw := coupled_weights A b hA hb hb1
  rw [hw.2.2.2.1, hw.2.2.2.2]
  rfl

theorem zero_weight_first_step {E : Type*} [AddCommGroup E] [Module ℝ E]
    (lam : ℝ) (hlam : 0 < lam) (x y : E) :
    (lam + Real.sqrt (lam ^ 2 + 4 * lam * 0)) / 2 = lam ∧
    (0 / (0 + lam)) • y + (lam / (0 + lam)) • x = x := by
  constructor
  · simp only [mul_zero, add_zero, Real.sqrt_sq_eq_abs, abs_of_pos hlam]
    ring
  · simp [ne_of_gt hlam]

theorem center_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (b c : ℝ) : ‖center x y b - center x y c‖ = |b - c| * ‖x - y‖ := by
  have heq : center x y b - center x y c = (b - c) • (x - y) := by dsimp [center]; module
  rw [heq, norm_smul, Real.norm_eq_abs]

theorem lambda_difference (A b c : ℝ) (hb : b ≠ 1) (hc : c ≠ 1) :
    lambda A b - lambda A c = A * (b - c) * (b + c - b * c) / ((1 - b) * (1 - c)) := by
  have hb' : 1 - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hc' : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  dsimp [lambda]
  field_simp <;> ring

theorem lambda_lipschitz_on_compact
    (A t b c : ℝ) (hA : 0 < A) (ht : 0 < t)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hbt : b ≤ 1 - t) (hct : c ≤ 1 - t) :
    |lambda A b - lambda A c| ≤ (2 * A / t ^ 2) * |b - c| := by
  have hb1 : b < 1 := by linarith
  have hc1 : c < 1 := by linarith
  have hden : 0 < (1 - b) * (1 - c) := by positivity
  have hdenlo : t ^ 2 ≤ (1 - b) * (1 - c) := by
    have hh := mul_le_mul (show t ≤ 1 - b by linarith) (show t ≤ 1 - c by linarith)
      ht.le (by linarith : 0 ≤ 1 - b)
    nlinarith only [hh]
  have hf0 : 0 ≤ b + c - b * c := by
    have hh := mul_nonneg hb (by linarith : 0 ≤ 1 - c)
    nlinarith only [hh, hc]
  have hf2 : b + c - b * c ≤ 2 := by
    have hh := mul_nonneg hb hc
    linarith only [hb1, hc1, hh]
  rw [lambda_difference A b c (ne_of_lt hb1) (ne_of_lt hc1), abs_div,
    abs_mul, abs_mul, abs_of_pos hA, abs_of_nonneg hf0, abs_of_pos hden]
  have hnum : A * |b - c| * (b + c - b * c) ≤ A * |b - c| * 2 :=
    mul_le_mul_of_nonneg_left hf2 (by positivity)
  have hinv : 1 / ((1 - b) * (1 - c)) ≤ 1 / t ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos ht) hdenlo
  calc
    _ = (A * |b - c| * (b + c - b * c)) * (1 / ((1 - b) * (1 - c))) := by ring
    _ ≤ (A * |b - c| * 2) * (1 / t ^ 2) :=
      mul_le_mul hnum hinv (by positivity) (by positivity)
    _ = (2 * A / t ^ 2) * |b - c| := by ring

end OriginalCoupledBetaAlgebra
end

section
-- Source component: TaylorProxStability.lean

namespace OriginalTaylorProxStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def proxGradient (v : E) (H : E →L[ℝ] E) (M lam : ℝ) (d : E) : E :=
  v + CertifiedATS.sympart H d + (M / 2 * ‖d‖) • d + lam⁻¹ • d

noncomputable def exactStep (v : E) (H : E →L[ℝ] E) (M lam : ℝ) : E :=
  Classical.epsilon (fun d => ∀ w, CertifiedATS.model v H M lam d ≤ CertifiedATS.model v H M lam w)

theorem model_strongConvex_with_prox
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    StrongConvexOn (Set.univ : Set E) (mu + lam⁻¹) (CertifiedATS.model v H M lam) := by
  let K := H + lam⁻¹ • ContinuousLinearMap.id ℝ E
  have hK : ∀ d : E, (mu + lam⁻¹) * ‖d‖ ^ 2 ≤ inner ℝ (K d) d := by
    intro d
    change (mu + lam⁻¹) * ‖d‖ ^ 2 ≤ inner ℝ (H d + lam⁻¹ • d) d
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith only [hcoer d]
  have hlin : ConvexOn ℝ (Set.univ : Set E) (fun d => inner ℝ v d) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [inner_add_right, inner_smul_right, smul_eq_mul, le_refl]
  have hcub : ConvexOn ℝ (Set.univ : Set E) (fun d => M / 6 * ‖d‖ ^ 3) := by
    simpa only [Pi.pow_apply, smul_eq_mul] using
      ConvexOn.smul (by positivity : 0 ≤ M / 6)
        (convexOn_univ_norm.pow (fun d _ => norm_nonneg d) 3)
  have hq := strongConvexOn_iff_convex.mp (CertifiedATS.quadratic_strongConvex K (mu + lam⁻¹) hK)
  have hh := (hq.add hlin).add hcub
  apply strongConvexOn_iff_convex.mpr
  convert! hh using 1
  funext d
  simp only [Pi.add_apply, CertifiedATS.model, K, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left]
  rw [real_inner_self_eq_norm_sq]
  field_simp <;> ring

theorem exactStep_minimizes
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    ∀ w : E, CertifiedATS.model v H M lam (exactStep v H M lam) ≤ CertifiedATS.model v H M lam w := by
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun d => (CertifiedATS.model_hasGradientAt v H M lam d).differentiableAt
  obtain ⟨d, hdmin⟩ := PacketCore.exists_inner_maximizer_finiteDimensional
    (CertifiedATS.model v H M lam) (mu + lam⁻¹) 0 0 0 0 hm
    (by simpa using model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd (0 : E)
  have hex : ∃ d : E, ∀ w : E, CertifiedATS.model v H M lam d ≤ CertifiedATS.model v H M lam w :=
    ⟨d, fun w => by simpa [PacketCore.saddleValue] using hdmin w⟩
  exact Classical.epsilon_spec hex

theorem exactStep_first_order
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    proxGradient v H M lam (exactStep v H M lam) = 0 := by
  exact CertifiedATS.model_minimum_first_order v H M lam _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer)

theorem distance_from_scaled_residual
    (v : E) (H : E →L[ℝ] E) (M lam mu sigma : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (d : E) (hres : ‖lam • proxGradient v H M lam d‖ ≤ sigma * ‖d‖) :
    ‖d - exactStep v H M lam‖ ≤ sigma * ‖d‖ := by
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) d
  rw [(CertifiedATS.model_hasGradientAt v H M lam d).gradient] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hlam.le
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at hres
  have hinv : lam * lam⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hlam)
  have hnonneg : 0 ≤ lam * mu * ‖d - exactStep v H M lam‖ := by positivity
  change lam * ((mu + lam⁻¹) * ‖d - exactStep v H M lam‖) ≤
    lam * ‖proxGradient v H M lam d‖ at hscaled
  change lam * ‖proxGradient v H M lam d‖ ≤ sigma * ‖d‖ at hres
  have hcoeff : lam * (mu + lam⁻¹) = lam * mu + 1 := by rw [mul_add, hinv]
  rw [← mul_assoc, hcoeff] at hscaled
  nlinarith only [hscaled, hres, hnonneg]

theorem approximate_norm_bracket
    (v : E) (H : E →L[ℝ] E) (M lam mu sigma : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (d : E) (hres : ‖lam • proxGradient v H M lam d‖ ≤ sigma * ‖d‖) :
    (1 - sigma) * ‖d‖ ≤ ‖exactStep v H M lam‖ ∧
      ‖exactStep v H M lam‖ ≤ (1 + sigma) * ‖d‖ := by
  have hd := distance_from_scaled_residual v H M lam mu sigma hM hlam hmu hcoer d hres
  have h1 := norm_le_norm_sub_add d (exactStep v H M lam)
  have h2 := norm_le_norm_sub_add (exactStep v H M lam) d
  rw [norm_sub_rev (exactStep v H M lam) d] at h2
  constructor <;> nlinarith only [hd, h1, h2]

theorem exactStep_size_bound
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    (mu + lam⁻¹) * ‖exactStep v H M lam‖ ≤ ‖v‖ := by
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) (0 : E)
  rw [(CertifiedATS.model_hasGradientAt v H M lam 0).gradient] at hs
  simpa only [zero_sub, norm_neg, map_zero, norm_zero, zero_smul, smul_zero, mul_zero, add_zero] using hs


theorem parameter_stability
    (v v' : E) (H H' : E →L[ℝ] E) (M lam lam' mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hlam' : 0 < lam') (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (hcoer' : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H' d) d) :
    (mu + lam⁻¹) * ‖exactStep v H M lam - exactStep v' H' M lam'‖ ≤
      ‖v - v'‖ + (‖CertifiedATS.sympart H - CertifiedATS.sympart H'‖ + |lam⁻¹ - lam'⁻¹|) *
        ‖exactStep v' H' M lam'‖ := by
  let d' := exactStep v' H' M lam'
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) d'
  rw [(CertifiedATS.model_hasGradientAt v H M lam d').gradient, norm_sub_rev d'] at hs
  have hz := exactStep_first_order v' H' M lam' mu hM hlam' hmu hcoer'
  have heq : proxGradient v H M lam d' = (v - v') +
      (CertifiedATS.sympart H - CertifiedATS.sympart H') d' + (lam⁻¹ - lam'⁻¹) • d' := by
    have heq0 : proxGradient v H M lam d' - proxGradient v' H' M lam' d' =
        (v - v') + (CertifiedATS.sympart H - CertifiedATS.sympart H') d' +
          (lam⁻¹ - lam'⁻¹) • d' := by
      dsimp [proxGradient]
      simp only [sub_apply, sub_smul]
      abel
    rw [hz, sub_zero] at heq0
    exact heq0
  change (mu + lam⁻¹) * ‖exactStep v H M lam - d'‖ ≤ ‖proxGradient v H M lam d'‖ at hs
  rw [heq] at hs
  have hnorm : ‖(v - v') + (CertifiedATS.sympart H - CertifiedATS.sympart H') d' +
      (lam⁻¹ - lam'⁻¹) • d'‖ ≤
      ‖v - v'‖ + (‖CertifiedATS.sympart H - CertifiedATS.sympart H'‖ + |lam⁻¹ - lam'⁻¹|) * ‖d'‖ := by
    calc
      _ ≤ ‖v - v'‖ + ‖(CertifiedATS.sympart H - CertifiedATS.sympart H') d'‖ +
          ‖(lam⁻¹ - lam'⁻¹) • d'‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖v - v'‖ + ‖CertifiedATS.sympart H - CertifiedATS.sympart H'‖ * ‖d'‖ +
          |lam⁻¹ - lam'⁻¹| * ‖d'‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact ContinuousLinearMap.le_opNorm (CertifiedATS.sympart H - CertifiedATS.sympart H') d' 
      _ = _ := by ring
  exact hs.trans hnorm

end OriginalTaylorProxStability
end

section
-- Source component: BetaCurveBounds.lean

namespace OriginalBetaCurveBounds

open OriginalCoupledBetaAlgebra
open OriginalTaylorProxStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem lambda_compact_bounds
    (A s t b : ℝ) (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hsb : s ≤ b) (hbt : b ≤ 1 - t) :
    A * s ^ 2 ≤ lambda A b ∧ lambda A b ≤ A / t := by
  have hb : 0 ≤ b := hs.le.trans hsb
  have hb1 : b < 1 := by linarith
  have hden : 0 < 1 - b := by linarith
  have hsquare : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.le hb).mpr hsb
  have hbSquare : b ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
  constructor
  · apply (le_div_iff₀ hden).mpr
    have h1 := mul_le_mul_of_nonneg_left (show 1 - b ≤ 1 by linarith) (by positivity : 0 ≤ A * s ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hsquare hA.le
    nlinarith only [h1, h2]
  · have hnum : A * b ^ 2 ≤ A := by nlinarith only [mul_le_mul_of_nonneg_left hbSquare hA.le]
    have hinv : 1 / (1 - b) ≤ 1 / t := one_div_le_one_div_of_le ht (by linarith)
    change A * b ^ 2 / (1 - b) ≤ A / t
    calc
      _ = (A * b ^ 2) * (1 / (1 - b)) := by ring
      _ ≤ A * (1 / t) := mul_le_mul hnum hinv (by positivity) hA.le
      _ = A / t := by ring

theorem reciprocal_lipschitz (a b m : ℝ) (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |a⁻¹ - b⁻¹| ≤ |a - b| / m ^ 2 := by
  have ha0 : 0 < a := hm.trans_le ha
  have hb0 : 0 < b := hm.trans_le hb
  have heq : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp <;> ring
  rw [heq, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm b a]
  have hprod : m ^ 2 ≤ a * b := by nlinarith only [mul_le_mul ha hb hm.le ha0.le]
  have hinv : 1 / (a * b) ≤ 1 / m ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos hm) hprod
  calc
    _ = |a - b| * (1 / (a * b)) := by ring
    _ ≤ |a - b| * (1 / m ^ 2) := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
    _ = |a - b| / m ^ 2 := by ring

theorem inverse_lambda_lipschitz_on_compact
    (A s t b c : ℝ) (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hsb : s ≤ b) (hsc : s ≤ c) (hbt : b ≤ 1 - t) (hct : c ≤ 1 - t) :
    |(lambda A b)⁻¹ - (lambda A c)⁻¹| ≤
      ((2 * A / t ^ 2) / (A * s ^ 2) ^ 2) * |b - c| := by
  have hb := lambda_compact_bounds A s t b hA hs ht hsb hbt
  have hc := lambda_compact_bounds A s t c hA hs ht hsc hct
  have hdiff := lambda_lipschitz_on_compact A t b c hA ht (hs.le.trans hsb) (hs.le.trans hsc) hbt hct
  calc
    _ ≤ |lambda A b - lambda A c| / (A * s ^ 2) ^ 2 :=
      reciprocal_lipschitz _ _ _ (by positivity) hb.1 hc.1
    _ ≤ ((2 * A / t ^ 2) * |b - c|) / (A * s ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hdiff (by positivity)
    _ = _ := by ring

noncomputable def gradientBound (g : E → ℝ) (Lg : ℝ) (x y : E) : ℝ :=
  ‖gradient g y‖ + Lg * ‖x - y‖

noncomputable def actualStep (g : E → ℝ) (M : ℝ) (z : E) (lam : ℝ) : E :=
  exactStep (gradient g z) (fderiv ℝ (gradient g) z) M lam

noncomputable def betaStep (g : E → ℝ) (M A : ℝ) (x y : E) (b : ℝ) : E :=
  actualStep g M (center x y b) (lambda A b)

noncomputable def betaSize (g : E → ℝ) (M A : ℝ) (x y : E) (b : ℝ) : ℝ :=
  lambda A b * ‖betaStep g M A x y b‖

theorem center_gradient_bound
    (g : E → ℝ) (Lg : ℝ) (hLg : 0 ≤ Lg)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (x y : E) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ‖gradient g (center x y b)‖ ≤ gradientBound g Lg x y := by
  have hz : ‖center x y b - y‖ ≤ ‖x - y‖ := by
    have heq : center x y b - y = b • (x - y) := by dsimp [center]; module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    nlinarith only [mul_le_mul_of_nonneg_right hb1 (norm_nonneg (x - y))]
  have ht := norm_le_norm_sub_add (gradient g (center x y b)) (gradient g y)
  have hh := (hlip (center x y b) y).trans (mul_le_mul_of_nonneg_left hz hLg)
  dsimp [gradientBound]
  linarith only [ht, hh]

theorem actualStep_uniform_bound
    (g : E → ℝ) (mu Lg M lam : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hC2 : ContDiff ℝ 2 g)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (x y : E) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ‖actualStep g M (center x y b) lam‖ ≤ gradientBound g Lg x y / mu := by
  have hs := exactStep_size_bound (gradient g (center x y b)) (fderiv ℝ (gradient g) (center x y b))
    M lam mu hM hlam hmu.le (CertifiedATS.actual_hessian_coercive g hC2 mu hsc (center x y b))
  have hg := center_gradient_bound g Lg hLg hlip x y b hb hb1
  have hnonneg : 0 ≤ lam⁻¹ * ‖actualStep g M (center x y b) lam‖ := by positivity
  apply (le_div_iff₀ hmu).mpr
  change (mu + lam⁻¹) * ‖actualStep g M (center x y b) lam‖ ≤ _ at hs
  nlinarith only [hs, hg, hnonneg]


noncomputable def inverseLambdaModulus (A s t : ℝ) : ℝ := (2 * A / t ^ 2) / (A * s ^ 2) ^ 2

noncomputable def stepModulus (mu Lg M A s t G D : ℝ) : ℝ :=
  (Lg * D + (M * D + inverseLambdaModulus A s t) * (G / mu)) / mu

noncomputable def sizeModulus (mu Lg M A s t G D : ℝ) : ℝ :=
  (2 * A / t ^ 2) * (G / mu) + (A / t) * stepModulus mu Lg M A s t G D

theorem betaStep_lipschitz
    (g : E → ℝ) (mu Lg M A s t G : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M)
    (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ M * ‖z - w‖)
    (x y : E) (hG : gradientBound g Lg x y ≤ G)
    (b c : ℝ) (hsb : s ≤ b) (hsc' : s ≤ c) (hbt : b ≤ 1 - t) (hct : c ≤ 1 - t) :
    ‖betaStep g M A x y b - betaStep g M A x y c‖ ≤
      stepModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by
  have hb0 : 0 ≤ b := hs.le.trans hsb
  have hc0 : 0 ≤ c := hs.le.trans hsc'
  have hb1 : b < 1 := by linarith
  have hc1 : c < 1 := by linarith
  have hblam := (coupled_weights A b hA (hs.trans_le hsb) hb1).1
  have hclam := (coupled_weights A c hA (hs.trans_le hsc') hc1).1
  have hcRadius : ‖betaStep g M A x y c‖ ≤ G / mu :=
    (actualStep_uniform_bound g mu Lg M _ hmu hLg hM hclam hC2 hsc hlip x y c hc0 hc1.le).trans
      (div_le_div_of_nonneg_right hG hmu.le)
  have hraw := parameter_stability (gradient g (center x y b)) (gradient g (center x y c))
    (fderiv ℝ (gradient g) (center x y b)) (fderiv ℝ (gradient g) (center x y c)) M
    (lambda A b) (lambda A c) mu hM hblam hclam hmu.le
    (CertifiedATS.actual_hessian_coercive g hC2 mu hsc _)
    (CertifiedATS.actual_hessian_coercive g hC2 mu hsc _)
  rw [CertifiedATS.sympart_eq_of_selfadjoint _ (CertifiedATS.gradient_derivative_selfadjoint g hC2 _),
    CertifiedATS.sympart_eq_of_selfadjoint _ (CertifiedATS.gradient_derivative_selfadjoint g hC2 _)] at hraw
  have hz := center_lipschitz x y b c
  have hv : ‖gradient g (center x y b) - gradient g (center x y c)‖ ≤ Lg * ‖x - y‖ * |b - c| := by
    calc
      _ ≤ Lg * ‖center x y b - center x y c‖ := hlip _ _
      _ = _ := by rw [hz]; ring
  have hH : ‖fderiv ℝ (gradient g) (center x y b) - fderiv ℝ (gradient g) (center x y c)‖ ≤
      M * ‖x - y‖ * |b - c| := by
    calc
      _ ≤ M * ‖center x y b - center x y c‖ := hHlip _ _
      _ = _ := by rw [hz]; ring
  have hi := inverse_lambda_lipschitz_on_compact A s t b c hA hs ht hsb hsc' hbt hct
  have hG0 : 0 ≤ G := (by dsimp [gradientBound]; positivity : 0 ≤ gradientBound g Lg x y).trans hG
  have hbound : mu * ‖betaStep g M A x y b - betaStep g M A x y c‖ ≤
      (Lg * ‖x - y‖ + (M * ‖x - y‖ + inverseLambdaModulus A s t) * (G / mu)) * |b - c| := by
    have hnonneg : 0 ≤ (lambda A b)⁻¹ * ‖betaStep g M A x y b - betaStep g M A x y c‖ := by positivity
    have h1 : mu * ‖betaStep g M A x y b - betaStep g M A x y c‖ ≤
        (mu + (lambda A b)⁻¹) * ‖betaStep g M A x y b - betaStep g M A x y c‖ := by
      nlinarith only [hnonneg]
    refine h1.trans (hraw.trans ?_)
    have hcoef0 : 0 ≤ (M * ‖x - y‖ + inverseLambdaModulus A s t) * |b - c| := by
      dsimp [inverseLambdaModulus]
      positivity
    have hsum : ‖fderiv ℝ (gradient g) (center x y b) - fderiv ℝ (gradient g) (center x y c)‖ +
        |(lambda A b)⁻¹ - (lambda A c)⁻¹| ≤
        (M * ‖x - y‖ + inverseLambdaModulus A s t) * |b - c| := by
      calc
        _ ≤ M * ‖x - y‖ * |b - c| + ((2 * A / t ^ 2) / (A * s ^ 2) ^ 2) * |b - c| := add_le_add hH hi
        _ = _ := by dsimp [inverseLambdaModulus]; ring
    calc
      _ ≤ (Lg * ‖x - y‖ * |b - c|) +
          ((M * ‖x - y‖ + inverseLambdaModulus A s t) * |b - c|) * (G / mu) := by
        exact add_le_add hv (mul_le_mul hsum hcRadius (norm_nonneg _) hcoef0)
      _ = _ := by ring
  calc
    _ ≤ ((Lg * ‖x - y‖ + (M * ‖x - y‖ + inverseLambdaModulus A s t) * (G / mu)) * |b - c|) / mu :=
      (le_div_iff₀ hmu).mpr (by nlinarith only [hbound])
    _ = stepModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by dsimp [stepModulus]; ring

theorem betaSize_lipschitz
    (g : E → ℝ) (mu Lg M A s t G : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M)
    (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ M * ‖z - w‖)
    (x y : E) (hG : gradientBound g Lg x y ≤ G)
    (b c : ℝ) (hsb : s ≤ b) (hsc' : s ≤ c) (hbt : b ≤ 1 - t) (hct : c ≤ 1 - t) :
    |betaSize g M A x y b - betaSize g M A x y c| ≤
      sizeModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by
  have hb0 : 0 ≤ b := hs.le.trans hsb
  have hb1 : b < 1 := by linarith
  have hblam := (coupled_weights A b hA (hs.trans_le hsb) hb1).1
  have hclam := (coupled_weights A c hA (hs.trans_le hsc') (by linarith)).1
  have hG0 : 0 ≤ G := (by dsimp [gradientBound]; positivity : 0 ≤ gradientBound g Lg x y).trans hG
  have hRadius : ‖betaStep g M A x y b‖ ≤ G / mu :=
    (actualStep_uniform_bound g mu Lg M _ hmu hLg hM hblam hC2 hsc hlip x y b hb0 hb1.le).trans
      (div_le_div_of_nonneg_right hG hmu.le)
  have hlamDiff := lambda_lipschitz_on_compact A t b c hA ht hb0 (hs.le.trans hsc') hbt hct
  have hlamUpper := (lambda_compact_bounds A s t c hA hs ht hsc' hct).2
  have hStepDiff := betaStep_lipschitz g mu Lg M A s t G hmu hLg hM hA hs ht
    hC2 hsc hlip hHlip x y hG b c hsb hsc' hbt hct
  have hNormDiff := (abs_norm_sub_norm_le (betaStep g M A x y b) (betaStep g M A x y c)).trans hStepDiff
  unfold betaSize
  calc
    _ = |(lambda A b - lambda A c) * ‖betaStep g M A x y b‖ +
        lambda A c * (‖betaStep g M A x y b‖ - ‖betaStep g M A x y c‖)| := by congr 1; ring
    _ ≤ |(lambda A b - lambda A c) * ‖betaStep g M A x y b‖| +
        |lambda A c * (‖betaStep g M A x y b‖ - ‖betaStep g M A x y c‖)| := abs_add_le _ _
    _ = |lambda A b - lambda A c| * ‖betaStep g M A x y b‖ +
        lambda A c * |‖betaStep g M A x y b‖ - ‖betaStep g M A x y c‖| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_pos hclam]
    _ ≤ ((2 * A / t ^ 2) * |b - c|) * (G / mu) +
        (A / t) * (stepModulus mu Lg M A s t G ‖x - y‖ * |b - c|) := by gcongr
    _ = sizeModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by dsimp [sizeModulus]; ring

end OriginalBetaCurveBounds
end

section
-- Source component: BetaATSUniform.lean

namespace OriginalBetaATSUniform

noncomputable def uniformStepFloor (mu Lg M lo rho : ℝ) : ℝ :=
  CertifiedATS.stepFloor rho (Lg + mu / 4 + lo⁻¹) M

noncomputable def uniformTolerance (mu Lg M lo up sigma rho : ℝ) : ℝ :=
  min (rho / 8) (min (mu / 4)
    (min (sigma * uniformStepFloor mu Lg M lo rho / (2 * up)) (sigma / (2 * up))))

theorem uniformStepFloor_positive
    (mu Lg M lo rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hrho : 0 < rho) :
    0 < uniformStepFloor mu Lg M lo rho := by
  exact CertifiedATS.stepFloor_positive rho _ M hrho (by positivity) hM

theorem uniformTolerance_positive
    (mu Lg M lo up sigma rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hup : 0 < up) (hsigma : 0 < sigma) (hrho : 0 < rho) :
    0 < uniformTolerance mu Lg M lo up sigma rho := by
  have hell := uniformStepFloor_positive mu Lg M lo rho hmu hLg hM hlo hrho
  unfold uniformTolerance
  positivity

theorem uniformStepFloor_le
    (mu Lg M lo lam rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hlolam : lo ≤ lam) (hrho : 0 < rho) :
    uniformStepFloor mu Lg M lo rho ≤ CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M := by
  have hlam : 0 < lam := hlo.trans_le hlolam
  have hinv : lam⁻¹ ≤ lo⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hlo hlolam
  have hden : 0 < 8 * (Lg + mu / 4 + lam⁻¹ + M / 2) := by positivity
  have hdenle : 8 * (Lg + mu / 4 + lam⁻¹ + M / 2) ≤ 8 * (Lg + mu / 4 + lo⁻¹ + M / 2) := by linarith
  change min 1 (rho / (8 * (Lg + mu / 4 + lo⁻¹ + M / 2))) ≤
    min 1 (rho / (8 * (Lg + mu / 4 + lam⁻¹ + M / 2)))
  exact min_le_min le_rfl (div_le_div_of_nonneg_left hrho.le hden hdenle)

theorem uniformTolerance_le_refinementTolerance
    (mu Lg M lo up lam sigma rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hlolam : lo ≤ lam) (hlamup : lam ≤ up)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    uniformTolerance mu Lg M lo up sigma rho ≤
      CertifiedATS.refinementTolerance mu Lg M lam sigma rho := by
  have hlam : 0 < lam := hlo.trans_le hlolam
  have hup : 0 < up := hlam.trans_le hlamup
  have hfloor := uniformStepFloor_le mu Lg M lo lam rho hmu hLg hM hlo hlolam hrho
  have hell : 0 < CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M :=
    CertifiedATS.stepFloor_positive rho _ M hrho (by positivity) hM
  have hterm3 : sigma * uniformStepFloor mu Lg M lo rho / (2 * up) ≤
      sigma * CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M / (2 * lam) := by
    calc
      _ ≤ sigma * CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M / (2 * up) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfloor hsigma.le) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hterm4 : sigma / (2 * up) ≤ sigma / (2 * lam) :=
    div_le_div_of_nonneg_left hsigma.le (by positivity) (by linarith)
  have h1 : uniformTolerance mu Lg M lo up sigma rho ≤ rho / 8 := min_le_left _ _
  have h2 : uniformTolerance mu Lg M lo up sigma rho ≤ mu / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h3 : uniformTolerance mu Lg M lo up sigma rho ≤ sigma * uniformStepFloor mu Lg M lo rho / (2 * up) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : uniformTolerance mu Lg M lo up sigma rho ≤ sigma / (2 * up) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact le_min h1 (le_min h2 (le_min (h3.trans hterm3) (h4.trans hterm4)))

theorem uniform_geometric_refinement
    (mu Lg M lo up lam sigma rho error0 : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hlolam : lo ≤ lam) (hlamup : lam ≤ up)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    error0 / (2 : ℝ) ^ CertifiedATS.halvingCount error0
      (uniformTolerance mu Lg M lo up sigma rho) ≤
        CertifiedATS.refinementTolerance mu Lg M lam sigma rho := by
  have hup : 0 < up := (hlo.trans_le hlolam).trans_le hlamup
  have ht := uniformTolerance_positive mu Lg M lo up sigma rho hmu hLg hM hlo hup hsigma hrho
  exact (CertifiedATS.halving_precision error0 _ ht).trans
    (uniformTolerance_le_refinementTolerance mu Lg M lo up lam sigma rho
      hmu hLg hM hlo hlolam hlamup hsigma hrho)

end OriginalBetaATSUniform
end

section
-- Source component: BetaATSTrial.lean

namespace OriginalBetaATSTrial

open OriginalTaylorProxStability
open OriginalBetaATSUniform

inductive GetterProgram (Q A R : Type*) where
  | pure (result : R)
  | ask (request : Q) (next : A → GetterProgram Q A R)

noncomputable def execute {Q A R : Type*} (getter : Q → A) : GetterProgram Q A R → R × ℕ
  | .pure r => (r, 0)
  | .ask q next => let r := execute getter (next (getter q)); (r.1, r.2 + 1)

structure Answer (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  grad : E
  hess : E →L[ℝ] E

inductive TrialResult (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  | stop (point : E)
  | step (displacement : E) (outputAnswer : Answer E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def trialProgram (M lam delta rho deltaY : ℝ) (z : E) :
    GetterProgram (E × ℝ) (Answer E) (TrialResult E) := by
  classical
  exact .ask (z, delta) (fun a =>
    if ‖a.grad‖ + delta ≤ rho then .pure (.stop z) else
      let d := exactStep a.grad a.hess M lam
      .ask (z + d, deltaY) (fun aY =>
        if ‖aY.grad‖ + deltaY ≤ rho then .pure (.stop (z + d)) else .pure (.step d aY)))

noncomputable def trial (getter : E × ℝ → Answer E) (M lam delta rho deltaY : ℝ) (z : E) : TrialResult E :=
  (execute getter (trialProgram M lam delta rho deltaY z)).1

def TrialSpec (g : E → ℝ) (M lam sigma rho deltaY : ℝ) (z : E) : TrialResult E → Prop
  | .stop w => ‖gradient g w‖ ≤ rho
  | .step d aY =>
      ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖ ∧
      ‖aY.grad - gradient g (z + d)‖ ≤ deltaY ∧ rho / 2 < ‖gradient g (z + d)‖

theorem exactStep_unique
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (d : E) (hmin : ∀ w : E, CertifiedATS.model v H M lam d ≤ CertifiedATS.model v H M lam w) :
    d = exactStep v H M lam := by
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) d
  rw [PacketCore.gradient_eq_zero_at_global_min _ _ hmin, norm_zero] at hs
  have hn : ‖d - exactStep v H M lam‖ ≤ 0 := by
    apply (mul_le_mul_iff_right₀ hm).mp
    simpa only [mul_zero] using hs
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

theorem selected_approximate_step_accepts
    (g : E → ℝ) (mu Lg M lam sigma rho delta : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (z v : E) (H : E →L[ℝ] E)
    (hgerr : ‖v - gradient g z‖ ≤ delta) (hHerr : ‖H - fderiv ℝ (gradient g) z‖ ≤ delta)
    (hsmall : delta ≤ CertifiedATS.refinementTolerance mu Lg M lam sigma rho)
    (haway : rho / 2 ≤ ‖gradient g z‖) :
    ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M (exactStep v H M lam) +
      exactStep v H M lam‖ ≤ sigma * ‖exactStep v H M lam‖ := by
  obtain ⟨d, hmin, hfloor, hcert, hATS⟩ := CertifiedATS.model_acceptance_at_accuracy g hC2
    mu Lg M lam sigma rho hmu hLg hM hlam hsigma hrho hsc hlip z v H delta hgerr hHerr hsmall haway
  have hdmu : delta ≤ mu / 4 := hsmall.trans (CertifiedATS.refinementTolerance_bounds mu Lg M lam sigma rho).2.1
  have hcoer : ∀ w : E, (3 * mu / 4) * ‖w‖ ^ 2 ≤ inner ℝ (H w) w := by
    intro w
    simpa only [CertifiedATS.sympart_same_quadratic] using
      CertifiedATS.approximate_hessian_coercive g hC2 mu hsc z H delta hHerr hdmu w
  have heq := exactStep_unique v H M lam (3 * mu / 4) hM hlam (by positivity) hcoer d hmin
  rwa [heq] at hATS

theorem trial_getter_calls
    (getter : E × ℝ → Answer E) (M lam delta rho deltaY : ℝ) (z : E) :
    (execute getter (trialProgram M lam delta rho deltaY z)).2 ≤ 2 := by
  classical
  by_cases hc : ‖(getter (z, delta)).grad‖ + delta ≤ rho
  · simp [trialProgram, execute, hc]
  · let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
    by_cases ho : ‖(getter (z + d, deltaY)).grad‖ + deltaY ≤ rho
    · dsimp only [d] at ho
      simp [trialProgram, execute, hc, d, ho]
    · dsimp only [d] at ho
      simp [trialProgram, execute, hc, d, ho]

theorem trial_spec_at_accuracy
    (g : E → ℝ) (mu Lg M lam sigma rho delta deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (hdelta : 0 < delta)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (z : E) (hsmall : delta ≤ CertifiedATS.refinementTolerance mu Lg M lam sigma rho) :
    TrialSpec g M lam sigma rho deltaY z (trial getter M lam delta rho deltaY z) := by
  classical
  have herr := hgetter z delta hdelta
  have hdeltaSmall := hsmall.trans (CertifiedATS.refinementTolerance_bounds mu Lg M lam sigma rho).1
  by_cases hcenter : ‖(getter (z, delta)).grad‖ + delta ≤ rho
  · simpa only [trial, trialProgram, execute, if_pos hcenter, TrialSpec] using
      CertifiedATS.center_stop_certifies _ _ delta rho herr.1 hcenter
  · let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
    have herrY := (hgetter (z + d) deltaY hdeltaY).1
    by_cases hout : ‖(getter (z + d, deltaY)).grad‖ + deltaY ≤ rho
    · dsimp only [d] at hout
      simpa only [trial, trialProgram, execute, d, if_neg hcenter, if_pos hout, TrialSpec] using
        CertifiedATS.center_stop_certifies _ _ deltaY rho herrY hout
    · dsimp only [d] at hout
      have hcenterAway : rho / 2 ≤ ‖gradient g z‖ := by
        have hn := norm_le_norm_sub_add (getter (z, delta)).grad (gradient g z)
        have hnot : rho < ‖(getter (z, delta)).grad‖ + delta := lt_of_not_ge hcenter
        linarith only [hn, herr.1, hdeltaSmall, hnot, hrho]
      have hATS := selected_approximate_step_accepts g mu Lg M lam sigma rho delta
        hmu hLg hM hlam hsigma hrho hC2 hsc hlip z _ _ herr.1 herr.2 hsmall hcenterAway
      have hawayY : rho / 2 < ‖gradient g (z + d)‖ := by
        have hn := norm_le_norm_sub_add (getter (z + d, deltaY)).grad (gradient g (z + d))
        have hnot : rho < ‖(getter (z + d, deltaY)).grad‖ + deltaY := lt_of_not_ge hout
        linarith only [hn, herrY, hdeltaYsmall, hnot, hrho]
      have hs : TrialSpec g M lam sigma rho deltaY z (.step d (getter (z + d, deltaY))) :=
        ⟨hATS, herrY, hawayY⟩
      simpa only [trial, trialProgram, execute, d, if_neg hcenter, if_neg hout] using hs

theorem trial_uniform_spec
    (g : E → ℝ) (mu Lg M lo up lam sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hlo : 0 < lo)
    (hlolam : lo ≤ lam) (hlamup : lam ≤ up) (hsigma : 0 < sigma) (hrho : 0 < rho)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (z : E) :
    TrialSpec g M lam sigma rho deltaY z
      (trial getter M lam (uniformTolerance mu Lg M lo up sigma rho) rho deltaY z) := by
  have hlam : 0 < lam := hlo.trans_le hlolam
  have hup : 0 < up := hlam.trans_le hlamup
  exact trial_spec_at_accuracy g mu Lg M lam sigma rho _ deltaY
    hmu hLg hM hlam hsigma hrho
    (uniformTolerance_positive mu Lg M lo up sigma rho hmu hLg hM hlo hup hsigma hrho)
    hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter z
    (uniformTolerance_le_refinementTolerance mu Lg M lo up lam sigma rho hmu hLg hM hlo hlolam hlamup hsigma hrho)

end OriginalBetaATSTrial
end

section
-- Source component: Upper02DependencyExtract02.lean

namespace RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_differentiable (F : E → ℝ) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (gradient F) := by
  have hder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have heq : gradient F = fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F y) := rfl
  rw [heq]
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hder).differentiable (by norm_num)


theorem scalarization_hasGradientAt (T : E → E) (hdiff : Differentiable ℝ T) (w x : E) :
    HasGradientAt (fun u : E => inner ℝ w (T u)) ((fderiv ℝ T x).adjoint w) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := (InnerProductSpace.toDual ℝ E w).hasFDerivAt.comp x (hdiff x).hasFDerivAt
  convert! hh using 1
  ext d
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem scalarization_gradient_lipschitz (T : E → E) (hdiff : Differentiable ℝ T)
    (M : ℝ) (hT : ∀ x y : E, ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ M * ‖x - y‖)
    (w x y : E) :
    ‖gradient (fun u : E => inner ℝ w (T u)) x - gradient (fun u : E => inner ℝ w (T u)) y‖ ≤
      (M * ‖w‖) * ‖x - y‖ := by
  rw [(scalarization_hasGradientAt T hdiff w x).gradient,
    (scalarization_hasGradientAt T hdiff w y).gradient]
  have he : (fderiv ℝ T x).adjoint w - (fderiv ℝ T y).adjoint w =
      (fderiv ℝ T x - fderiv ℝ T y).adjoint w := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [he]
  have hn := ContinuousLinearMap.le_opNorm (fderiv ℝ T x - fderiv ℝ T y).adjoint w
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  have hm := mul_le_mul_of_nonneg_right (hT x y) (norm_nonneg w)
  nlinarith only [hn, hm]

theorem vector_taylor_remainder (T : E → E) (hdiff : Differentiable ℝ T)
    (M : ℝ) (hM : 0 < M)
    (hT : ∀ x y : E, ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ M * ‖x - y‖)
    (z d : E) : ‖T (z + d) - T z - fderiv ℝ T z d‖ ≤ M / 2 * ‖d‖ ^ 2 := by
  let R := T (z + d) - T z - fderiv ℝ T z d
  by_cases hz : R = 0
  · change ‖R‖ ≤ M / 2 * ‖d‖ ^ 2
    rw [hz, norm_zero]
    positivity
  · have hR : 0 < ‖R‖ := norm_pos_iff.mpr hz
    let p : E → ℝ := fun u => inner ℝ R (T u)
    have hp : Differentiable ℝ p := fun u => (scalarization_hasGradientAt T hdiff R u).differentiableAt
    have hupper := OriginalAudit.smooth_descent_upper p (M * ‖R‖) (by positivity) hp
      (scalarization_gradient_lipschitz T hdiff M hT R) z d
    have hgrad : gradient p z = (fderiv ℝ T z).adjoint R :=
      (scalarization_hasGradientAt T hdiff R z).gradient
    rw [hgrad, ContinuousLinearMap.adjoint_inner_left] at hupper
    have hi : inner ℝ R (T (z + d)) - inner ℝ R (T z) - inner ℝ R (fderiv ℝ T z d) = ‖R‖ ^ 2 := by
      rw [← inner_sub_right, ← inner_sub_right]
      exact real_inner_self_eq_norm_sq R
    dsimp only [p] at hupper
    have hsq : ‖R‖ * ‖R‖ ≤ ‖R‖ * (M / 2 * ‖d‖ ^ 2) := by
      nlinarith only [hupper, hi]
    change ‖R‖ ≤ M / 2 * ‖d‖ ^ 2
    exact (mul_le_mul_iff_right₀ hR).mp (by nlinarith only [hsq])

theorem gradient_taylor_remainder (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M : ℝ) (hM : 0 < M)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) : ‖gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d‖ ≤
      M / 2 * ‖d‖ ^ 2 :=
  vector_taylor_remainder (gradient g) (gradient_differentiable g hC2) M hM hH z d

end RobustAHPE

namespace RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def trueModelVector (g : E → ℝ) (z : E) (Mbar : ℝ) (d : E) : E :=
  gradient g z + fderiv ℝ (gradient g) z d + (Mbar / 2 * ‖d‖) • d

theorem gradient_minus_modelVector_bound (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M Mbar : ℝ) (hM : 0 < M) (hMbar : 0 ≤ Mbar)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) : ‖gradient g (z + d) - trueModelVector g z Mbar d‖ ≤
      (M + Mbar) / 2 * ‖d‖ ^ 2 := by
  have ht := gradient_taylor_remainder g hC2 M hM hH z d
  have he : gradient g (z + d) - trueModelVector g z Mbar d =
      (gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d) - (Mbar / 2 * ‖d‖) • d := by
    dsimp only [trueModelVector]
    abel
  rw [he]
  have hn : ‖(Mbar / 2 * ‖d‖) • d‖ = (Mbar / 2) * ‖d‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  have htri := norm_sub_le
    (gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d) ((Mbar / 2 * ‖d‖) • d)
  rw [hn] at htri
  nlinarith only [ht, htri]

theorem true_gradient_residual_from_ATS (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M lam sigmaHat sigmaU : ℝ) (hM : 0 < M) (hlam : 0 < lam)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaU / M) :
    ‖lam • gradient g (z + d) + d‖ ≤ (sigmaHat + sigmaU) * ‖d‖ := by
  have hm := gradient_minus_modelVector_bound g hC2 M M hM hM.le hH z d
  have he : lam • gradient g (z + d) + d =
      (lam • trueModelVector g z M d + d) + lam • (gradient g (z + d) - trueModelVector g z M d) := by
    module
  rw [he]
  have htri := norm_add_le (lam • trueModelVector g z M d + d)
    (lam • (gradient g (z + d) - trueModelVector g z M d))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at htri
  have hmul := mul_le_mul_of_nonneg_left hm hlam.le
  have hw := (le_div_iff₀ hM).mp hwindow
  have hwmul := mul_le_mul_of_nonneg_right hw (norm_nonneg d)
  nlinarith only [htri, hATS, hmul, hwmul]

theorem new_gradient_bound_from_ATS (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M lam sigmaHat sigmaU : ℝ) (hM : 0 < M) (hlam : 0 < lam)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaU / M) :
    ‖gradient g (z + d)‖ ≤ (1 + sigmaHat + sigmaU) * ‖d‖ / lam := by
  have hr := true_gradient_residual_from_ATS g hC2 M lam sigmaHat sigmaU hM hlam hH z d hATS hwindow
  have ht := norm_sub_le (lam • gradient g (z + d) + d) d
  have he : (lam • gradient g (z + d) + d) - d = lam • gradient g (z + d) := by abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at ht
  apply (le_div_iff₀ hlam).mpr
  nlinarith only [ht, hr]

theorem large_lambda_gradient_endpoint (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M lam sigmaHat sigmaU : ℝ) (hM : 0 < M) (hlam : 0 < lam)
    (hsigmaHat : 0 ≤ sigmaHat) (hsigmaU : 0 ≤ sigmaU)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaU / M) :
    ‖gradient g (z + d)‖ ≤ (1 + sigmaHat + sigmaU) * sigmaU / (M * lam ^ 2) := by
  have hg := new_gradient_bound_from_ATS g hC2 M lam sigmaHat sigmaU hM hlam hH z d hATS hwindow
  have hw : ‖d‖ ≤ sigmaU / (M * lam) := by
    apply (le_div_iff₀ (mul_pos hM hlam)).mpr
    have hh := (le_div_iff₀ hM).mp hwindow
    nlinarith only [hh]
  calc
    ‖gradient g (z + d)‖ ≤ (1 + sigmaHat + sigmaU) * ‖d‖ / lam := hg
    _ ≤ (1 + sigmaHat + sigmaU) * (sigmaU / (M * lam)) / lam := by gcongr
    _ = (1 + sigmaHat + sigmaU) * sigmaU / (M * lam ^ 2) := by field_simp <;> ring

end RobustAHPE
end

section
-- Source component: BetaSearchEndpoints.lean

namespace OriginalBetaSearchEndpoints

open OriginalCoupledBetaAlgebra
open OriginalTaylorProxStability
open OriginalBetaCurveBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem gradient_upper_from_certificate
    (g : E → ℝ) (Lg : ℝ) (x y v : E) (delta : ℝ)
    (herr : ‖v - gradient g y‖ ≤ delta) :
    gradientBound g Lg x y ≤ ‖v‖ + delta + Lg * ‖x - y‖ := by
  have hn := norm_le_norm_sub_add (gradient g y) v
  rw [norm_sub_rev (gradient g y) v] at hn
  dsimp [gradientBound]
  linarith only [hn, herr]

theorem actual_scaled_residual
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (M lam : ℝ) (hlam : 0 < lam) (z d : E) :
    lam • proxGradient (gradient g z) (fderiv ℝ (gradient g) z) M lam d =
      lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d := by
  dsimp [proxGradient, CertifiedATS.trueVector]
  rw [CertifiedATS.sympart_eq_of_selfadjoint _ (CertifiedATS.gradient_derivative_selfadjoint g hC2 z)]
  simp only [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hlam), one_smul]

theorem actual_approximate_norm_bracket
    (g : E → ℝ) (mu M lam sigma : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖) :
    (1 - sigma) * (lam * ‖d‖) ≤ lam * ‖actualStep g M z lam‖ ∧
      lam * ‖actualStep g M z lam‖ ≤ (1 + sigma) * (lam * ‖d‖) := by
  have hr : ‖lam • proxGradient (gradient g z) (fderiv ℝ (gradient g) z) M lam d‖ ≤ sigma * ‖d‖ := by
    rw [actual_scaled_residual g hC2 M lam hlam z d]
    exact hATS
  have hn := approximate_norm_bracket (gradient g z) (fderiv ℝ (gradient g) z) M lam mu sigma
    hM hlam hmu.le (CertifiedATS.actual_hessian_coercive g hC2 mu hsc z) d hr
  change (1 - sigma) * ‖d‖ ≤ ‖actualStep g M z lam‖ ∧
    ‖actualStep g M z lam‖ ≤ (1 + sigma) * ‖d‖ at hn
  constructor
  · have hh := mul_le_mul_of_nonneg_left hn.1 hlam.le
    nlinarith only [hh]
  · have hh := mul_le_mul_of_nonneg_left hn.2 hlam.le
    nlinarith only [hh]

theorem exact_step_lambda_bound
    (g : E → ℝ) (mu M lam G : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z : E) (hG : ‖gradient g z‖ ≤ G) : ‖actualStep g M z lam‖ ≤ lam * G := by
  have hh := exactStep_size_bound (gradient g z) (fderiv ℝ (gradient g) z) M lam mu hM hlam hmu.le
    (CertifiedATS.actual_hessian_coercive g hC2 mu hsc z)
  have hm := mul_le_mul_of_nonneg_left (hh.trans hG) hlam.le
  have hinv : lam * (mu + lam⁻¹) = lam * mu + 1 := by
    rw [mul_add, mul_inv_cancel₀ (ne_of_gt hlam)]
  change lam * ((mu + lam⁻¹) * ‖actualStep g M z lam‖) ≤ lam * G at hm
  rw [← mul_assoc, hinv] at hm
  have hn : 0 ≤ lam * mu * ‖actualStep g M z lam‖ := by positivity
  nlinarith only [hm, hn]

theorem approximate_small_lambda_bound
    (g : E → ℝ) (mu M lam sigma G : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E) (hG : ‖gradient g z‖ ≤ G)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖) :
    (1 - sigma) * (lam * ‖d‖) ≤ lam ^ 2 * G := by
  have hb := (actual_approximate_norm_bracket g mu M lam sigma hmu hM hlam hC2 hsc z d hATS).1
  have hs := exact_step_lambda_bound g mu M lam G hmu hM hlam hC2 hsc z hG
  have hm := mul_le_mul_of_nonneg_left hs hlam.le
  nlinarith only [hb, hm]

noncomputable def lambdaLow (M sigmaLow sigma G : ℝ) : ℝ :=
  min 1 (sigmaLow * (1 - sigma) / (2 * M * (1 + G)))

noncomputable def lambdaHigh (M rho sigma sigmaUp : ℝ) : ℝ :=
  1 + 2 * ((1 + sigma + sigmaUp) * sigmaUp) / (M * rho)

noncomputable def betaLow (A ell : ℝ) : ℝ := min (1 / 4) (ell / (4 * (1 + A)))
noncomputable def highMargin (A H : ℝ) : ℝ := min (1 / 4) (A / (8 * (1 + H)))
noncomputable def betaHigh (A H : ℝ) : ℝ := 1 - highMargin A H

theorem lambdaLow_positive
    (M sigmaLow sigma G : ℝ) (hM : 0 < M) (hLow : 0 < sigmaLow) (hsigma : sigma < 1) (hG : 0 ≤ G) :
    0 < lambdaLow M sigmaLow sigma G ∧ lambdaLow M sigmaLow sigma G ≤ 1 := by
  exact ⟨lt_min zero_lt_one (by positivity), min_le_left _ _⟩

theorem betaLow_properties
    (A ell : ℝ) (hA : 0 < A) (hell : 0 < ell) :
    0 < betaLow A ell ∧ betaLow A ell ≤ 1 / 4 ∧ lambda A (betaLow A ell) ≤ ell := by
  let b := betaLow A ell
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  have hb4 : b ≤ 1 / 4 := min_le_left _ _
  have hbell : b ≤ ell / (4 * (1 + A)) := min_le_right _ _
  have hden : 0 < 1 - b := by linarith
  have hinv : 1 / (1 - b) ≤ 2 := by apply (div_le_iff₀ hden).mpr; linarith
  have hb2 : b ^ 2 ≤ b := by nlinarith only [hb, hb4]
  refine ⟨hb, hb4, ?_⟩
  change A * b ^ 2 / (1 - b) ≤ ell
  calc
    _ = (A * b ^ 2) * (1 / (1 - b)) := by ring
    _ ≤ (A * b) * 2 := mul_le_mul (mul_le_mul_of_nonneg_left hb2 hA.le) hinv (by positivity) (by positivity)
    _ ≤ (A * (ell / (4 * (1 + A)))) * 2 := by gcongr
    _ ≤ ell := by
      have heq : (A * (ell / (4 * (1 + A)))) * 2 = (2 * A * ell) / (4 * (1 + A)) := by ring
      rw [heq]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (1 + A))).mpr
      nlinarith only [hA, hell]

theorem betaHigh_properties
    (A H : ℝ) (hA : 0 < A) (hH : 0 ≤ H) :
    0 < highMargin A H ∧ highMargin A H ≤ 1 / 4 ∧
    3 / 4 ≤ betaHigh A H ∧ betaHigh A H < 1 ∧ H ≤ lambda A (betaHigh A H) := by
  let t := highMargin A H
  let b := betaHigh A H
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht4 : t ≤ 1 / 4 := min_le_left _ _
  have htA : t ≤ A / (8 * (1 + H)) := min_le_right _ _
  have hb : 3 / 4 ≤ b := by dsimp [b, betaHigh]; linarith only [ht4]
  have hb1 : b < 1 := by dsimp [b, betaHigh]; linarith only [ht]
  refine ⟨ht, ht4, hb, hb1, ?_⟩
  have hb2 : (1 / 4 : ℝ) ≤ b ^ 2 := by nlinarith only [hb]
  have hAprod := (le_div_iff₀ (by positivity : 0 < 8 * (1 + H))).mp htA
  have hlow : H ≤ (A / 4) / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith only [hAprod, ht, hH]
  have hquad := mul_le_mul_of_nonneg_left hb2 hA.le
  have heq : 1 - b = t := by dsimp [b, betaHigh, t]; ring
  change H ≤ A * b ^ 2 / (1 - b)
  rw [heq]
  exact hlow.trans (div_le_div_of_nonneg_right (by nlinarith only [hquad]) ht.le)


theorem low_endpoint_is_low
    (g : E → ℝ) (mu Lg M A sigmaLow sigma G : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 < M) (hA : 0 < A)
    (hLow : 0 < sigmaLow) (hsigma : sigma < 1) (hG0 : 0 ≤ G)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (x y d : E) (hG : gradientBound g Lg x y ≤ G)
    (hATS : let b := betaLow A (lambdaLow M sigmaLow sigma G)
      ‖lambda A b • CertifiedATS.trueVector (gradient g (center x y b))
        (fderiv ℝ (gradient g) (center x y b)) M d + d‖ ≤ sigma * ‖d‖) :
    lambda A (betaLow A (lambdaLow M sigmaLow sigma G)) * ‖d‖ < sigmaLow / M := by
  let ell := lambdaLow M sigmaLow sigma G
  let b := betaLow A ell
  let lam := lambda A b
  have hell := lambdaLow_positive M sigmaLow sigma G hM hLow hsigma hG0
  have hb := betaLow_properties A ell hA hell.1
  have hb1 : b < 1 := by linarith only [hb.2.1]
  have hlam : 0 < lam := (coupled_weights A b hA hb.1 hb1).1
  have hlamEll : lam ≤ ell := hb.2.2
  have hlamOne : lam ≤ 1 := hlamEll.trans hell.2
  have hprod := mul_nonneg hlam.le (sub_nonneg.mpr hlamOne)
  have hsq : lam ^ 2 ≤ ell := by nlinarith only [hprod, hlamEll]
  have hgrad : ‖gradient g (center x y b)‖ ≤ G :=
    (center_gradient_bound g Lg hLg hlip x y b hb.1.le hb1.le).trans hG
  have hsmall := approximate_small_lambda_bound g mu M lam sigma G hmu hM.le hlam hC2 hsc
    (center x y b) d hgrad hATS
  have hratio : ell ≤ sigmaLow * (1 - sigma) / (2 * M * (1 + G)) := min_le_right _ _
  have hr := (le_div_iff₀ (by positivity : 0 < 2 * M * (1 + G))).mp hratio
  have hellG : ell * G ≤ sigmaLow * (1 - sigma) / (2 * M) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * M)).mpr
    have hn : 0 ≤ 2 * M * ell := mul_nonneg (by positivity) hell.1.le
    nlinarith only [hr, hn]
  have hscale : (1 - sigma) * (lam * ‖d‖) ≤ (1 - sigma) * (sigmaLow / (2 * M)) := by
    calc
      _ ≤ lam ^ 2 * G := hsmall
      _ ≤ ell * G := mul_le_mul_of_nonneg_right hsq hG0
      _ ≤ sigmaLow * (1 - sigma) / (2 * M) := hellG
      _ = _ := by ring
  have hs : lam * ‖d‖ ≤ sigmaLow / (2 * M) :=
    (mul_le_mul_iff_right₀ (show 0 < 1 - sigma by linarith)).mp hscale
  have hhalf : sigmaLow / (2 * M) < sigmaLow / M := by
    have hp : 0 < sigmaLow / M := div_pos hLow hM
    have heq : sigmaLow / (2 * M) = (sigmaLow / M) / 2 := by ring
    rw [heq]
    linarith only [hp]
  exact hs.trans_lt hhalf

theorem large_lambda_upper_is_small
    (g : E → ℝ) (M rho sigma sigmaUp lam : ℝ)
    (hM : 0 < M) (hrho : 0 < rho) (hsigma : 0 ≤ sigma) (hUp : 0 ≤ sigmaUp)
    (hlam : 0 < lam) (hlarge : lambdaHigh M rho sigma sigmaUp ≤ lam)
    (hC2 : ContDiff ℝ 2 g)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ M * ‖z - w‖)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaUp / M) : ‖gradient g (z + d)‖ ≤ rho / 2 := by
  let C := (1 + sigma + sigmaUp) * sigmaUp
  let q := 2 * C / (M * rho)
  have hq : 0 ≤ q := by dsimp [q, C]; positivity
  have hlarge' : 1 + q ≤ lam := hlarge
  have hsquare : q ≤ lam ^ 2 := by nlinarith only [hlarge', hq, sq_nonneg q]
  have hmul := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ M * rho)
  have heq : (M * rho) * q = 2 * C := by dsimp [q]; field_simp
  rw [heq] at hmul
  have hfinal : C / (M * lam ^ 2) ≤ rho / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < M * lam ^ 2)).mpr
    nlinarith only [hmul]
  have hb := RobustAHPE.large_lambda_gradient_endpoint g hC2 M lam sigma sigmaUp
    hM hlam hsigma hUp hHlip z d hATS hwindow
  exact hb.trans hfinal

theorem low_failure_exact_threshold
    (g : E → ℝ) (mu M lam sigma sigmaLow : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (hsigma : 0 ≤ sigma)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hlow : lam * ‖d‖ < sigmaLow / M) :
    lam * ‖actualStep g M z lam‖ ≤ sigmaLow * (1 + sigma) / M := by
  have hb := (actual_approximate_norm_bracket g mu M lam sigma hmu hM.le hlam hC2 hsc z d hATS).2
  have hm := mul_le_mul_of_nonneg_left hlow.le (by positivity : 0 ≤ 1 + sigma)
  have heq : (1 + sigma) * (sigmaLow / M) = sigmaLow * (1 + sigma) / M := by ring
  exact hb.trans (by simpa only [heq] using hm)

theorem high_failure_exact_threshold
    (g : E → ℝ) (mu M lam sigma sigmaUp : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (hsigma : sigma < 1)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hhigh : sigmaUp / M < lam * ‖d‖) :
    sigmaUp * (1 - sigma) / M ≤ lam * ‖actualStep g M z lam‖ := by
  have hb := (actual_approximate_norm_bracket g mu M lam sigma hmu hM.le hlam hC2 hsc z d hATS).1
  have hm := mul_le_mul_of_nonneg_left hhigh.le (show 0 ≤ 1 - sigma by linarith)
  have heq : (1 - sigma) * (sigmaUp / M) = sigmaUp * (1 - sigma) / M := by ring
  have hm' : sigmaUp * (1 - sigma) / M ≤ (1 - sigma) * (lam * ‖d‖) := by
    simpa only [heq] using hm
  exact hm'.trans hb

end OriginalBetaSearchEndpoints
end

section
-- Source component: HysteresisBisection.lean

namespace FangqingHysteresis

inductive Decision (R : Type*) where
  | accept (value : R)
  | low
  | high

inductive Outcome (R : Type*) where
  | found (value : R)
  | bracket (left right : ℝ)

inductive Program (Reply Result : Type*) where
  | pure (value : Result)
  | ask (point : ℝ) (next : Reply → Program Reply Result)

noncomputable def execute {Reply Result : Type*} (oracle : ℝ → Reply) :
    Program Reply Result → Result × ℕ
  | .pure value => (value, 0)
  | .ask x next => let r := execute oracle (next (oracle x)); (r.1, r.2 + 1)

noncomputable def bisect {R : Type*} : ℕ → ℝ → ℝ → Program (Decision R) (Outcome R)
  | 0, l, r => .pure (.bracket l r)
  | n + 1, l, r =>
      let m := (l + r) / 2
      .ask m (fun answer => match answer with
        | .accept value => .pure (.found value)
        | .low => bisect n m r
        | .high => bisect n l m)

def Bracket (F : ℝ → ℝ) (a b L U l r : ℝ) : Prop :=
  L ≤ l ∧ l ≤ r ∧ r ≤ U ∧ F l ≤ a ∧ b ≤ F r

def Spec {R : Type*} (F : ℝ → ℝ) (P : R → Prop) (a b L U : ℝ)
    (fuel : ℕ) (l r : ℝ) : Outcome R → Prop
  | .found value => P value
  | .bracket l' r' => Bracket F a b L U l' r' ∧ r' - l' = (r - l) / (2 : ℝ) ^ fuel

theorem execution_calls_le_fuel {R : Type*} (trial : ℝ → Decision R)
    (fuel : ℕ) (l r : ℝ) : (execute trial (bisect fuel l r)).2 ≤ fuel := by
  induction fuel generalizing l r with
  | zero => simp [bisect, execute]
  | succ n ih =>
    cases htrial : trial ((l + r) / 2) with
    | accept value => simp [bisect, execute, htrial]
    | low =>
      simpa only [bisect, execute, htrial] using Nat.add_le_add_right (ih ((l + r) / 2) r) 1
    | high =>
      simpa only [bisect, execute, htrial] using Nat.add_le_add_right (ih l ((l + r) / 2)) 1

theorem run_spec {R : Type*} (trial : ℝ → Decision R) (F : ℝ → ℝ) (P : R → Prop)
    (a b L U : ℝ)
    (haccept : ∀ x ∈ Set.Icc L U, ∀ value, trial x = .accept value → P value)
    (hlow : ∀ x ∈ Set.Icc L U, trial x = .low → F x ≤ a)
    (hhigh : ∀ x ∈ Set.Icc L U, trial x = .high → b ≤ F x)
    (fuel : ℕ) (l r : ℝ) (hbracket : Bracket F a b L U l r) :
    Spec F P a b L U fuel l r (execute trial (bisect fuel l r)).1 := by
  induction fuel generalizing l r with
  | zero =>
    simp only [bisect, execute, Spec, pow_zero, div_one]
    exact ⟨hbracket, True.intro⟩
  | succ n ih =>
    rcases hbracket with ⟨hl, hlr, hr, hFl, hFr⟩
    let m := (l + r) / 2
    have hm : m ∈ Set.Icc L U := ⟨by dsimp only [m]; linarith, by dsimp only [m]; linarith⟩
    cases htrial : trial ((l + r) / 2) with
    | accept value =>
      simp only [bisect, execute, htrial, Spec]
      exact haccept m hm value htrial
    | low =>
      have hnew : Bracket F a b L U m r :=
        ⟨hm.1, by dsimp only [m]; linarith, hr, hlow m hm htrial, hFr⟩
      have hi := ih m r hnew
      simp only [bisect, execute, htrial]
      cases hres : (execute trial (bisect n m r)).1 with
      | found value => simpa only [hres, Spec] using hi
      | bracket l' r' =>
        simp only [hres, Spec] at hi ⊢
        refine ⟨hi.1, ?_⟩
        rw [hi.2]
        dsimp only [m]
        rw [pow_succ]
        field_simp
        <;> ring
    | high =>
      have hnew : Bracket F a b L U l m :=
        ⟨hl, by dsimp only [m]; linarith, hm.2, hFl, hhigh m hm htrial⟩
      have hi := ih l m hnew
      simp only [bisect, execute, htrial]
      cases hres : (execute trial (bisect n l m)).1 with
      | found value => simpa only [hres, Spec] using hi
      | bracket l' r' =>
        simp only [hres, Spec] at hi ⊢
        refine ⟨hi.1, ?_⟩
        rw [hi.2]
        dsimp only [m]
        rw [pow_succ]
        field_simp
        <;> ring

noncomputable def halvingCount (a tau : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (max 1 (a / tau)))

theorem halving_precision (a tau : ℝ) (htau : 0 < tau) :
    a / (2 : ℝ) ^ halvingCount a tau ≤ tau := by
  have hm : 0 < max 1 (a / tau) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hn : Real.logb 2 (max 1 (a / tau)) ≤ (halvingCount a tau : ℝ) := Nat.le_ceil _
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hn
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hm,
    Real.rpow_natCast] at hp
  have hh := le_trans (le_max_right 1 (a / tau)) hp
  have hmul := (div_le_iff₀ htau).mp hh
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  nlinarith only [hmul]

noncomputable def searchFuel (K L U a b : ℝ) : ℕ :=
  halvingCount (K * (U - L)) ((b - a) / 2)

theorem bisection_success_and_calls {R : Type*}
    (trial : ℝ → Decision R) (F : ℝ → ℝ) (P : R → Prop)
    (a b L U K : ℝ) (hgap : a < b) (hK : 0 ≤ K)
    (hLU : L ≤ U) (hL : F L ≤ a) (hU : b ≤ F U)
    (hLip : ∀ x ∈ Set.Icc L U, ∀ y ∈ Set.Icc L U, |F x - F y| ≤ K * |x - y|)
    (haccept : ∀ x ∈ Set.Icc L U, ∀ value, trial x = .accept value → P value)
    (hlow : ∀ x ∈ Set.Icc L U, trial x = .low → F x ≤ a)
    (hhigh : ∀ x ∈ Set.Icc L U, trial x = .high → b ≤ F x) :
    ∃ value : R,
      (execute trial (bisect (searchFuel K L U a b) L U)).1 = .found value ∧ P value ∧
      (execute trial (bisect (searchFuel K L U a b) L U)).2 ≤ searchFuel K L U a b := by
  let n := searchFuel K L U a b
  have hspec := run_spec trial F P a b L U haccept hlow hhigh n L U
    ⟨le_rfl, hLU, le_rfl, hL, hU⟩
  cases hout : (execute trial (bisect n L U)).1 with
  | found value =>
    refine ⟨value, rfl, ?_, execution_calls_le_fuel trial n L U⟩
    simpa only [hout, Spec] using hspec
  | bracket l r =>
    simp only [hout, Spec, Bracket] at hspec
    rcases hspec with ⟨⟨hl, hlr, hr, hFl, hFr⟩, hwidth⟩
    have hlI : l ∈ Set.Icc L U := ⟨hl, le_trans hlr hr⟩
    have hrI : r ∈ Set.Icc L U := ⟨le_trans hl hlr, hr⟩
    have hdiff := hLip r hrI l hlI
    rw [abs_of_nonneg (sub_nonneg.mpr hlr)] at hdiff
    have hfg : b - a ≤ F r - F l := by linarith only [hFl, hFr]
    have hg : b - a ≤ K * (r - l) := hfg.trans ((le_abs_self _).trans hdiff)
    have hsmall := halving_precision (K * (U - L)) ((b - a) / 2) (by linarith only [hgap])
    change K * (U - L) / (2 : ℝ) ^ n ≤ (b - a) / 2 at hsmall
    have heq : K * (r - l) = K * (U - L) / (2 : ℝ) ^ n := by rw [hwidth]; ring
    rw [heq] at hg
    exfalso
    linarith only [hg, hsmall, hgap]

theorem searchFuel_log_bound (K L U a b : ℝ) :
    (searchFuel K L U a b : ℝ) ≤
      1 + Real.logb 2 (max 1 ((K * (U - L)) / ((b - a) / 2))) := by
  unfold searchFuel halvingCount
  have h0 : 0 ≤ Real.logb 2 (max 1 ((K * (U - L)) / ((b - a) / 2))) :=
    Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have h := Nat.ceil_lt_add_one h0
  linarith only [h]

end FangqingHysteresis
end

section
-- Source component: CoupledBetaSearch.lean

namespace OriginalCoupledBetaSearch

open OriginalCoupledBetaAlgebra
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints
open OriginalBetaATSUniform
open OriginalBetaATSTrial (Answer TrialResult)
open FangqingHysteresis (Decision Outcome)

structure Settings where
  mu : ℝ
  Lg : ℝ
  M : ℝ
  A : ℝ
  sigma : ℝ
  sigmaLow : ℝ
  sigmaUp : ℝ
  rho : ℝ

structure Legal (c : Settings) : Prop where
  mu_pos : 0 < c.mu
  Lg_nonneg : 0 ≤ c.Lg
  M_pos : 0 < c.M
  A_pos : 0 < c.A
  sigma_pos : 0 < c.sigma
  sigma_lt_one : c.sigma < 1
  low_pos : 0 < c.sigmaLow
  low_lt_up : c.sigmaLow < c.sigmaUp
  gap : c.sigmaLow * (1 + c.sigma) < c.sigmaUp * (1 - c.sigma)
  rho_pos : 0 < c.rho

noncomputable def lower (c : Settings) (G : ℝ) : ℝ :=
  betaLow c.A (lambdaLow c.M c.sigmaLow c.sigma G)
noncomputable def margin (c : Settings) : ℝ :=
  highMargin c.A (lambdaHigh c.M c.rho c.sigma c.sigmaUp)
noncomputable def upper (c : Settings) : ℝ := 1 - margin c
noncomputable def lambdaMin (c : Settings) (G : ℝ) : ℝ := c.A * lower c G ^ 2
noncomputable def lambdaMax (c : Settings) : ℝ := c.A / margin c
noncomputable def tolerance (c : Settings) (G : ℝ) : ℝ :=
  uniformTolerance c.mu c.Lg c.M (lambdaMin c G) (lambdaMax c) c.sigma c.rho
noncomputable def thresholdLow (c : Settings) : ℝ := c.sigmaLow * (1 + c.sigma) / c.M
noncomputable def thresholdHigh (c : Settings) : ℝ := c.sigmaUp * (1 - c.sigma) / c.M

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def modulus (c : Settings) (G : ℝ) (x y : E) : ℝ :=
  sizeModulus c.mu c.Lg c.M c.A (lower c G) (margin c) G ‖x - y‖

noncomputable def observedGradientBound (getter : E × ℝ → Answer E) (c : Settings) (x y : E) : ℝ :=
  ‖(getter (y, 1)).grad‖ + 1 + c.Lg * ‖x - y‖

inductive Result (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  | stop (point : E)
  | window (beta : ℝ) (displacement : E) (outputAnswer : Answer E)

noncomputable def classifiedTrial (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (x y : E) (b : ℝ) : Decision (Result E) := by
  classical
  exact match OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
    | .stop w => .accept (.stop w)
    | .step d aY =>
        if c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M then
          .accept (.window b d aY)
        else if lambda c.A b * ‖d‖ < c.sigmaLow / c.M then .low else .high

def ValidResult (g : E → ℝ) (c : Settings) (G deltaY : ℝ) (x y : E) : Result E → Prop
  | .stop w => ‖gradient g w‖ ≤ c.rho
  | .window b d aY =>
      b ∈ Set.Icc (lower c G) (upper c) ∧ 0 < b ∧ b < 1 ∧
      0 < lambda c.A b ∧
      c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M ∧
      ‖lambda c.A b • CertifiedATS.trueVector (gradient g (center x y b))
        (fderiv ℝ (gradient g) (center x y b)) c.M d + d‖ ≤ c.sigma * ‖d‖ ∧
      ‖aY.grad - gradient g (center x y b + d)‖ ≤ deltaY ∧
      weight c.A b = (lambda c.A b + Real.sqrt (lambda c.A b ^ 2 + 4 * lambda c.A b * c.A)) / 2 ∧
      center x y b = (c.A / (c.A + weight c.A b)) • y +
        (weight c.A b / (c.A + weight c.A b)) • x

theorem compact_properties (c : Settings) (hc : Legal c) (G : ℝ) (hG : 0 ≤ G) :
    0 < lower c G ∧ lower c G ≤ 1 / 4 ∧ 0 < margin c ∧ margin c ≤ 1 / 4 ∧
    3 / 4 ≤ upper c ∧ upper c < 1 ∧ lower c G ≤ upper c ∧
    0 < lambdaMin c G ∧ 0 < lambdaMax c := by
  have hLow := lambdaLow_positive c.M c.sigmaLow c.sigma G hc.M_pos hc.low_pos hc.sigma_lt_one hG
  have hlo := betaLow_properties c.A _ hc.A_pos hLow.1
  have hu : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hHigh : 0 ≤ lambdaHigh c.M c.rho c.sigma c.sigmaUp := by
    dsimp [lambdaHigh]
    have hm := hc.M_pos
    have hr := hc.rho_pos
    have hs := hc.sigma_pos
    positivity
  have hhi := betaHigh_properties c.A _ hc.A_pos hHigh
  have hrange : lower c G ≤ upper c := by
    change betaLow c.A _ ≤ betaHigh c.A _
    linarith only [hlo.2.1, hhi.2.2.1]
  refine ⟨hlo.1, hlo.2.1, hhi.1, hhi.2.1, hhi.2.2.1, hhi.2.2.2.1, hrange, ?_, ?_⟩
  · exact mul_pos hc.A_pos (sq_pos_of_pos hlo.1)
  · exact div_pos hc.A_pos hhi.1

theorem interval_lambda_bounds (c : Settings) (hc : Legal c) (G : ℝ) (hG : 0 ≤ G)
    (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c)) :
    0 < b ∧ b < 1 ∧ 0 < lambda c.A b ∧
      lambdaMin c G ≤ lambda c.A b ∧ lambda c.A b ≤ lambdaMax c := by
  have hp := compact_properties c hc G hG
  have hb0 : 0 < b := hp.1.trans_le hb.1
  have hb1 : b < 1 := hb.2.trans_lt hp.2.2.2.2.2.1
  have hlam := (coupled_weights c.A b hc.A_pos hb0 hb1).1
  have hh := lambda_compact_bounds c.A (lower c G) (margin c) b hc.A_pos hp.1 hp.2.2.1 hb.1 hb.2
  exact ⟨hb0, hb1, hlam, hh.1, hh.2⟩

theorem observed_bound_is_valid
    (g : E → ℝ) (c : Settings) (hc : Legal c) (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    0 ≤ observedGradientBound getter c x y ∧
      gradientBound g c.Lg x y ≤ observedGradientBound getter c x y := by
  refine ⟨?_, ?_⟩
  · dsimp [observedGradientBound]
    have hLg := hc.Lg_nonneg
    positivity
  · exact gradient_upper_from_certificate g c.Lg x y _ 1 (hgetter y 1 (by norm_num)).1

theorem interval_trial_spec
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c)) :
    OriginalBetaATSTrial.TrialSpec g c.M (lambda c.A b) c.sigma c.rho deltaY (center x y b)
      (OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b)) := by
  have hp := compact_properties c hc G hG
  have hl := interval_lambda_bounds c hc G hG b hb
  exact OriginalBetaATSTrial.trial_uniform_spec g c.mu c.Lg c.M (lambdaMin c G) (lambdaMax c)
    (lambda c.A b) c.sigma c.rho deltaY hc.mu_pos hc.Lg_nonneg hc.M_pos.le
    hp.2.2.2.2.2.2.2.1 hl.2.2.2.1 hl.2.2.2.2 hc.sigma_pos hc.rho_pos
    hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter (center x y b)


theorem actual_modulus_spec
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G : ℝ) (hG0 : 0 ≤ G)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G) :
    0 ≤ modulus c G x y ∧
    (∀ b ∈ Set.Icc (lower c G) (upper c), ∀ d ∈ Set.Icc (lower c G) (upper c),
      |betaSize g c.M c.A x y b - betaSize g c.M c.A x y d| ≤ modulus c G x y * |b - d|) := by
  have hp := compact_properties c hc G hG0
  have hmu := hc.mu_pos
  have hLg := hc.Lg_nonneg
  have hM := hc.M_pos
  have hA := hc.A_pos
  have hlo := hp.1
  have ht := hp.2.2.1
  refine ⟨?_, ?_⟩
  · dsimp [modulus, sizeModulus, stepModulus, inverseLambdaModulus]
    positivity
  · intro b hb d hd
    exact betaSize_lipschitz g c.mu c.Lg c.M c.A (lower c G) (margin c) G
      hc.mu_pos hc.Lg_nonneg hc.M_pos.le hc.A_pos hp.1 hp.2.2.1 hC2 hsc hlip hHlip
      x y hG b d hb.1 hd.1 hb.2 hd.2

theorem threshold_gap (c : Settings) (hc : Legal c) : thresholdLow c < thresholdHigh c :=
  div_lt_div_of_pos_right hc.gap hc.M_pos

theorem classified_accept_valid
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (value : Result E) (haccept : classifiedTrial getter c G deltaY x y b = .accept value) :
    ValidResult g c G deltaY x y value := by
  classical
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb
  have hl := interval_lambda_bounds c hc G hG0 b hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
  | stop w =>
    simp only [classifiedTrial, hr] at haccept
    have hv := Decision.accept.inj haccept
    rw [← hv]
    rw [hr] at ht
    exact ht
  | step d aY =>
    rw [hr] at ht
    by_cases hw : c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M
    · simp only [classifiedTrial, hr, if_pos hw] at haccept
      have hv := Decision.accept.inj haccept
      rw [← hv]
      exact ⟨hb, hl.1, hl.2.1, hl.2.2.1, hw.1, hw.2, ht.1, ht.2.1,
        coupled_square_root_formula c.A b hc.A_pos hl.1 hl.2.1,
        (coupled_center c.A b hc.A_pos hl.1 hl.2.1 x y).symm⟩
    · simp only [classifiedTrial, hr, if_neg hw] at haccept
      split_ifs at haccept <;> cases haccept

theorem classified_low_threshold
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (hlow : classifiedTrial getter c G deltaY x y b = .low) :
    betaSize g c.M c.A x y b ≤ thresholdLow c := by
  classical
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb
  have hl := interval_lambda_bounds c hc G hG0 b hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
  | stop w => simp only [classifiedTrial, hr] at hlow; cases hlow
  | step d aY =>
    rw [hr] at ht
    by_cases hw : c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M
    · simp only [classifiedTrial, hr, if_pos hw] at hlow; cases hlow
    · by_cases hm : lambda c.A b * ‖d‖ < c.sigmaLow / c.M
      · exact low_failure_exact_threshold g c.mu c.M (lambda c.A b) c.sigma c.sigmaLow
          hc.mu_pos hc.M_pos hl.2.2.1 hc.sigma_pos.le hC2 hsc (center x y b) d ht.1 hm
      · simp only [classifiedTrial, hr, if_neg hw, if_neg hm] at hlow; cases hlow

theorem classified_high_threshold
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (hhigh : classifiedTrial getter c G deltaY x y b = .high) :
    thresholdHigh c ≤ betaSize g c.M c.A x y b := by
  classical
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb
  have hl := interval_lambda_bounds c hc G hG0 b hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
  | stop w => simp only [classifiedTrial, hr] at hhigh; cases hhigh
  | step d aY =>
    rw [hr] at ht
    by_cases hw : c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M
    · simp only [classifiedTrial, hr, if_pos hw] at hhigh; cases hhigh
    · by_cases hm : lambda c.A b * ‖d‖ < c.sigmaLow / c.M
      · simp only [classifiedTrial, hr, if_neg hw, if_pos hm] at hhigh; cases hhigh
      · have hbound : c.sigmaUp / c.M < lambda c.A b * ‖d‖ := by
          apply lt_of_not_ge
          intro hle
          exact hw ⟨le_of_not_gt hm, hle⟩
        exact high_failure_exact_threshold g c.mu c.M (lambda c.A b) c.sigma c.sigmaUp
          hc.mu_pos hc.M_pos hl.2.2.1 hc.sigma_lt_one hC2 hsc (center x y b) d ht.1 hbound


theorem lower_endpoint_not_high
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G) :
    classifiedTrial getter c G deltaY x y (lower c G) ≠ .high := by
  classical
  intro hhigh
  have hp := compact_properties c hc G hG0
  have hb : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A (lower c G)) (tolerance c G)
      c.rho deltaY (center x y (lower c G)) with
  | stop w => simp only [classifiedTrial, hr] at hhigh; cases hhigh
  | step d aY =>
    rw [hr] at ht
    have hs := low_endpoint_is_low g c.mu c.Lg c.M c.A c.sigmaLow c.sigma G
      hc.mu_pos hc.Lg_nonneg hc.M_pos hc.A_pos hc.low_pos hc.sigma_lt_one hG0 hC2 hsc hlip x y d hG ht.1
    change lambda c.A (lower c G) * ‖d‖ < c.sigmaLow / c.M at hs
    have hn : ¬(c.sigmaLow / c.M ≤ lambda c.A (lower c G) * ‖d‖ ∧
        lambda c.A (lower c G) * ‖d‖ ≤ c.sigmaUp / c.M) := by
      intro hw
      exact not_le_of_gt hs hw.1
    simp only [classifiedTrial, hr, if_neg hn, if_pos hs] at hhigh
    cases hhigh

theorem upper_endpoint_not_low
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) : classifiedTrial getter c G deltaY x y (upper c) ≠ .low := by
  classical
  intro hlow
  have hp := compact_properties c hc G hG0
  have hb : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hb
  have hl := interval_lambda_bounds c hc G hG0 (upper c) hb
  have hUp : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hHigh0 : 0 ≤ lambdaHigh c.M c.rho c.sigma c.sigmaUp := by
    dsimp [lambdaHigh]
    have hM := hc.M_pos
    have hRho := hc.rho_pos
    have hSigma := hc.sigma_pos
    positivity
  have hlarge := (betaHigh_properties c.A (lambdaHigh c.M c.rho c.sigma c.sigmaUp) hc.A_pos hHigh0).2.2.2.2
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A (upper c)) (tolerance c G)
      c.rho deltaY (center x y (upper c)) with
  | stop w => simp only [classifiedTrial, hr] at hlow; cases hlow
  | step d aY =>
    rw [hr] at ht
    have hs : c.sigmaUp / c.M < lambda c.A (upper c) * ‖d‖ := by
      apply lt_of_not_ge
      intro hwindow
      have hg := large_lambda_upper_is_small g c.M c.rho c.sigma c.sigmaUp (lambda c.A (upper c))
        hc.M_pos hc.rho_pos hc.sigma_pos.le hUp.le hl.2.2.1 hlarge hC2 hHlip (center x y (upper c)) d ht.1 hwindow
      exact not_lt_of_ge hg ht.2.2
    have hn : ¬(c.sigmaLow / c.M ≤ lambda c.A (upper c) * ‖d‖ ∧
        lambda c.A (upper c) * ‖d‖ ≤ c.sigmaUp / c.M) := by
      intro hw
      exact not_le_of_gt hs hw.2
    have hLowUp : c.sigmaLow / c.M < c.sigmaUp / c.M := div_lt_div_of_pos_right hc.low_lt_up hc.M_pos
    have hnotlow : ¬lambda c.A (upper c) * ‖d‖ < c.sigmaLow / c.M :=
      not_lt_of_ge (hLowUp.le.trans hs.le)
    simp only [classifiedTrial, hr, if_neg hn, if_neg hnotlow] at hlow
    cases hlow

noncomputable def fuel (c : Settings) (G : ℝ) (x y : E) : ℕ :=
  FangqingHysteresis.searchFuel (modulus c G x y) (lower c G) (upper c) (thresholdLow c) (thresholdHigh c)

noncomputable def searchProgram (c : Settings) (G : ℝ) (x y : E) :
    FangqingHysteresis.Program (Decision (Result E)) (Outcome (Result E)) :=
  .ask (lower c G) (fun left => match left with
    | .accept value => .pure (.found value)
    | _ => .ask (upper c) (fun right => match right with
      | .accept value => .pure (.found value)
      | _ => FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c)))

theorem bisection_after_endpoints
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G)
    (hleft : classifiedTrial getter c G deltaY x y (lower c G) = .low)
    (hright : classifiedTrial getter c G deltaY x y (upper c) = .high) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y)
        (FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c))).1 = .found value ∧
      ValidResult g c G deltaY x y value ∧
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y)
        (FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c))).2 ≤ fuel c G x y := by
  have hp := compact_properties c hc G hG0
  have hbL : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have hbU : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  have hK := actual_modulus_spec g c hc G hG0 hC2 hsc hlip hHlip x y hG
  exact FangqingHysteresis.bisection_success_and_calls
    (classifiedTrial getter c G deltaY x y) (betaSize g c.M c.A x y) (ValidResult g c G deltaY x y)
    (thresholdLow c) (thresholdHigh c) (lower c G) (upper c) (modulus c G x y)
    (threshold_gap c hc) hK.1 hp.2.2.2.2.2.2.1
    (classified_low_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbL hleft)
    (classified_high_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbU hright)
    hK.2
    (fun b hb value hv => classified_accept_valid g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb value hv)
    (fun b hb hv => classified_low_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb hv)
    (fun b hb hv => classified_high_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb hv)


noncomputable def classifyResult (c : Settings) (b : ℝ) : TrialResult E → Decision (Result E) := by
  classical
  exact fun raw => match raw with
    | .stop w => .accept (.stop w)
    | .step d aY =>
        if c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M then
          .accept (.window b d aY)
        else if lambda c.A b * ‖d‖ < c.sigmaLow / c.M then .low else .high

theorem classifiedTrial_factor (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (x y : E) (b : ℝ) :
    classifiedTrial getter c G deltaY x y b = classifyResult c b
      (OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b)) := rfl

theorem positive_search_success_and_calls
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y) (searchProgram c G x y)).1 = .found value ∧
      ValidResult g c G deltaY x y value ∧
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y) (searchProgram c G x y)).2 ≤ fuel c G x y + 2 := by
  have hp := compact_properties c hc G hG0
  have hbL : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have hbU : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  cases hleft : classifiedTrial getter c G deltaY x y (lower c G) with
  | accept value =>
    refine ⟨value, ?_, ?_, ?_⟩
    · simp only [searchProgram, FangqingHysteresis.execute, hleft]
    · exact classified_accept_valid g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbL value hleft
    · simp only [searchProgram, FangqingHysteresis.execute, hleft]
      omega
  | high => exact False.elim (lower_endpoint_not_high g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y hG hleft)
  | low =>
    cases hright : classifiedTrial getter c G deltaY x y (upper c) with
    | accept value =>
      refine ⟨value, ?_, ?_, ?_⟩
      · simp only [searchProgram, FangqingHysteresis.execute, hleft, hright]
      · exact classified_accept_valid g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbU value hright
      · simp only [searchProgram, FangqingHysteresis.execute, hleft, hright]
        omega
    | low => exact False.elim (upper_endpoint_not_low g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip hHlip getter hgetter x y hright)
    | high =>
      obtain ⟨value, hrun, hvalid, hcount⟩ := bisection_after_endpoints g c hc G deltaY hG0 hdeltaY hdeltaYsmall
        hC2 hsc hlip hHlip getter hgetter x y hG hleft hright
      refine ⟨value, ?_, hvalid, ?_⟩
      · simpa only [searchProgram, FangqingHysteresis.execute, hleft, hright] using hrun
      · simpa only [searchProgram, FangqingHysteresis.execute, hleft, hright, Nat.add_assoc] using Nat.add_le_add_right hcount 2

theorem positive_search_log_bound (c : Settings) (G : ℝ) (x y : E) :
    (fuel c G x y : ℝ) + 2 ≤
      3 + Real.logb 2 (max 1 (((modulus c G x y) * (upper c - lower c G)) /
        ((thresholdHigh c - thresholdLow c) / 2))) := by
  have h := FangqingHysteresis.searchFuel_log_bound (modulus c G x y) (lower c G) (upper c) (thresholdLow c) (thresholdHigh c)
  change (fuel c G x y : ℝ) ≤ _ at h
  linarith only [h]

end OriginalCoupledBetaSearch
end

section
-- Source component: GetterProgramAdapter.lean

namespace FangqingGetterComposition

open OriginalBetaATSTrial

noncomputable def bind {Q A R S : Type*} :
    GetterProgram Q A R → (R → GetterProgram Q A S) → GetterProgram Q A S
  | .pure r, next => next r
  | .ask q cont, next => .ask q (fun answer => bind (cont answer) next)

noncomputable def map {Q A R S : Type*} (f : R → S) (program : GetterProgram Q A R) :
    GetterProgram Q A S := bind program (fun r => .pure (f r))

theorem execute_bind {Q A R S : Type*} (getter : Q → A)
    (program : GetterProgram Q A R) (next : R → GetterProgram Q A S) :
    execute getter (bind program next) =
      ((execute getter (next (execute getter program).1)).1,
        (execute getter program).2 + (execute getter (next (execute getter program).1)).2) := by
  induction program with
  | pure r => simp only [bind, execute, zero_add]
  | ask q cont ih =>
    simp only [bind, execute, ih]
    exact Prod.ext rfl (by omega)

theorem execute_map {Q A R S : Type*} (getter : Q → A) (f : R → S)
    (program : GetterProgram Q A R) :
    execute getter (map f program) = (f (execute getter program).1, (execute getter program).2) := by
  simp only [map, execute_bind, execute, add_zero]

noncomputable def derivedReply {Q A Reply : Type*} (getter : Q → A)
    (trials : ℝ → GetterProgram Q A Reply) (point : ℝ) : Reply := (execute getter (trials point)).1

noncomputable def lower {Q A Reply Result : Type*} (trials : ℝ → GetterProgram Q A Reply) :
    FangqingHysteresis.Program Reply Result → GetterProgram Q A Result
  | .pure r => .pure r
  | .ask point cont => bind (trials point) (fun reply => lower trials (cont reply))

theorem lower_result_and_count {Q A Reply Result : Type*}
    (getter : Q → A) (trials : ℝ → GetterProgram Q A Reply) (K : ℕ)
    (htrial : ∀ point : ℝ, (execute getter (trials point)).2 ≤ K)
    (program : FangqingHysteresis.Program Reply Result) :
    (execute getter (lower trials program)).1 =
      (FangqingHysteresis.execute (derivedReply getter trials) program).1 ∧
    (execute getter (lower trials program)).2 ≤
      K * (FangqingHysteresis.execute (derivedReply getter trials) program).2 := by
  induction program with
  | pure r => simp only [lower, execute, FangqingHysteresis.execute, mul_zero, le_refl, and_self]
  | ask point cont ih =>
    have hi := ih (derivedReply getter trials point)
    have hc := htrial point
    simp only [lower, execute_bind, FangqingHysteresis.execute]
    constructor
    · exact hi.1
    · change (execute getter (trials point)).2 +
        (execute getter (lower trials (cont (derivedReply getter trials point)))).2 ≤
          K * ((FangqingHysteresis.execute (derivedReply getter trials)
            (cont (derivedReply getter trials point))).2 + 1)
      have hm := add_le_add hc hi.2
      nlinarith only [hm]

noncomputable def withInitial {Q A Reply Result : Type*} (request : Q)
    (trials : A → ℝ → GetterProgram Q A Reply)
    (program : A → FangqingHysteresis.Program Reply Result) : GetterProgram Q A Result :=
  .ask request (fun answer => lower (trials answer) (program answer))

theorem withInitial_result_and_count {Q A Reply Result : Type*}
    (getter : Q → A) (request : Q) (trials : A → ℝ → GetterProgram Q A Reply)
    (program : A → FangqingHysteresis.Program Reply Result) (K : ℕ)
    (htrial : ∀ answer point, (execute getter (trials answer point)).2 ≤ K) :
    (execute getter (withInitial request trials program)).1 =
      (FangqingHysteresis.execute (derivedReply getter (trials (getter request))) (program (getter request))).1 ∧
    (execute getter (withInitial request trials program)).2 ≤
      1 + K * (FangqingHysteresis.execute
        (derivedReply getter (trials (getter request))) (program (getter request))).2 := by
  have hi := lower_result_and_count getter (trials (getter request)) K (htrial (getter request))
    (program (getter request))
  simp only [withInitial, execute]
  exact ⟨hi.1, by omega⟩

section ActualTaylorTrials
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def mappedTaylorTrial {Reply : Type*}
    (classify : ℝ → TrialResult E → Reply)
    (M delta rho deltaY : ℝ) (lam : ℝ → ℝ) (center : ℝ → E) (point : ℝ) :
    GetterProgram (E × ℝ) (Answer E) Reply :=
  map (classify point) (trialProgram M (lam point) delta rho deltaY (center point))

theorem mappedTaylorTrial_calls {Reply : Type*}
    (getter : E × ℝ → Answer E) (classify : ℝ → TrialResult E → Reply)
    (M delta rho deltaY : ℝ) (lam : ℝ → ℝ) (center : ℝ → E) (point : ℝ) :
    (execute getter (mappedTaylorTrial classify M delta rho deltaY lam center point)).2 ≤ 2 := by
  rw [mappedTaylorTrial, execute_map]
  exact trial_getter_calls getter M (lam point) delta rho deltaY (center point)

theorem lowered_actual_trials_result_and_count {Reply Result : Type*}
    (getter : E × ℝ → Answer E) (classify : ℝ → TrialResult E → Reply)
    (M delta rho deltaY : ℝ) (lam : ℝ → ℝ) (center : ℝ → E)
    (program : FangqingHysteresis.Program Reply Result) :
    (execute getter (lower (mappedTaylorTrial classify M delta rho deltaY lam center) program)).1 =
      (FangqingHysteresis.execute
        (derivedReply getter (mappedTaylorTrial classify M delta rho deltaY lam center)) program).1 ∧
    (execute getter (lower (mappedTaylorTrial classify M delta rho deltaY lam center) program)).2 ≤
      2 * (FangqingHysteresis.execute
        (derivedReply getter (mappedTaylorTrial classify M delta rho deltaY lam center)) program).2 :=
  lower_result_and_count getter _ 2 (mappedTaylorTrial_calls getter classify M delta rho deltaY lam center) program

end ActualTaylorTrials
end FangqingGetterComposition

namespace FangqingGetterComposition
open OriginalBetaATSTrial

noncomputable def trace {Q A R : Type*} (getter : Q → A) : GetterProgram Q A R → List Q
  | .pure _ => []
  | .ask q next => q :: trace getter (next (getter q))

noncomputable def baseCost {Q A R : Type*} (getter : Q → A) (cost : Q → ℕ) : GetterProgram Q A R → ℕ
  | .pure _ => 0
  | .ask q next => cost q + baseCost getter cost (next (getter q))

def AllRequests {Q A R : Type*} (P : Q → Prop) : GetterProgram Q A R → Prop
  | .pure _ => True
  | .ask q next => P q ∧ ∀ answer : A, AllRequests P (next answer)

theorem trace_length_eq_count {Q A R : Type*} (getter : Q → A) (program : GetterProgram Q A R) :
    (trace getter program).length = (execute getter program).2 := by
  induction program with
  | pure r => rfl
  | ask q next ih => simp only [trace, execute, List.length_cons, ih]

theorem baseCost_eq_trace_sum {Q A R : Type*}
    (getter : Q → A) (cost : Q → ℕ) (program : GetterProgram Q A R) :
    baseCost getter cost program = ((trace getter program).map cost).sum := by
  induction program with
  | pure r => rfl
  | ask q next ih => simp only [baseCost, trace, List.map_cons, List.sum_cons, ih]

theorem allRequests_trace {Q A R : Type*} (getter : Q → A) (P : Q → Prop)
    (program : GetterProgram Q A R) (hprogram : AllRequests P program) :
    ∀ q ∈ trace getter program, P q := by
  induction program with
  | pure r => simp only [trace, List.not_mem_nil, false_implies, implies_true]
  | ask q next ih =>
    intro req hmem
    simp only [trace, List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact hprogram.1
    · exact ih (getter q) (hprogram.2 (getter q)) req htail

theorem allRequests_bind {Q A R S : Type*} (P : Q → Prop)
    (program : GetterProgram Q A R) (next : R → GetterProgram Q A S)
    (hprogram : AllRequests P program) (hnext : ∀ r : R, AllRequests P (next r)) :
    AllRequests P (bind program next) := by
  induction program with
  | pure r => exact hnext r
  | ask q cont ih =>
    exact ⟨hprogram.1, fun answer => ih answer (hprogram.2 answer)⟩

theorem allRequests_map {Q A R S : Type*} (P : Q → Prop) (f : R → S)
    (program : GetterProgram Q A R) (hprogram : AllRequests P program) : AllRequests P (map f program) :=
  allRequests_bind P program _ hprogram (fun _ => True.intro)

theorem allRequests_lower {Q A Reply Result : Type*}
    (P : Q → Prop) (trials : ℝ → GetterProgram Q A Reply)
    (htrials : ∀ point : ℝ, AllRequests P (trials point))
    (program : FangqingHysteresis.Program Reply Result) : AllRequests P (lower trials program) := by
  induction program with
  | pure r => exact True.intro
  | ask point cont ih => exact allRequests_bind P (trials point) _ (htrials point) ih

theorem trace_withInitial_requests {Q A Reply Result : Type*}
    (getter : Q → A) (request : Q) (trials : A → ℝ → GetterProgram Q A Reply)
    (program : A → FangqingHysteresis.Program Reply Result) (P : Q → Prop)
    (hinitial : P request) (htrials : ∀ point : ℝ, AllRequests P (trials (getter request) point)) :
    ∀ q ∈ trace getter (withInitial request trials program), P q := by
  intro q hq
  simp only [withInitial, trace, List.mem_cons] at hq
  rcases hq with rfl | htail
  · exact hinitial
  · exact allRequests_trace getter P _ (allRequests_lower P _ htrials _) q htail

theorem list_cost_bound {Q : Type*} (requests : List Q) (cost : Q → ℕ) (C : ℕ)
    (hcost : ∀ q ∈ requests, cost q ≤ C) : (requests.map cost).sum ≤ C * requests.length := by
  induction requests with
  | nil => simp
  | cons q tail ih =>
    have hh := hcost q (by simp)
    have ht := ih (fun r hr => hcost r (by simp [hr]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith only [hh, ht]

theorem baseCost_le_mul_count {Q A R : Type*}
    (getter : Q → A) (cost : Q → ℕ) (program : GetterProgram Q A R) (C : ℕ)
    (hcost : ∀ q ∈ trace getter program, cost q ≤ C) :
    baseCost getter cost program ≤ C * (execute getter program).2 := by
  rw [baseCost_eq_trace_sum]
  simpa only [trace_length_eq_count] using list_cost_bound (trace getter program) cost C hcost

section TaylorRequestPrecisions
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem trialProgram_precision_set (M lam delta rho deltaY : ℝ) (z : E) :
    AllRequests (fun q : E × ℝ => q.2 = delta ∨ q.2 = deltaY)
      (trialProgram M lam delta rho deltaY z) := by
  classical
  unfold trialProgram
  change (delta = delta ∨ delta = deltaY) ∧ _
  refine ⟨Or.inl rfl, ?_⟩
  intro a
  dsimp only
  split_ifs
  · exact True.intro
  · change (deltaY = delta ∨ deltaY = deltaY) ∧ _
    refine ⟨Or.inr rfl, ?_⟩
    intro aY
    dsimp only
    split_ifs <;> exact True.intro

theorem mappedTaylorTrial_precision_set {Reply : Type*}
    (classify : ℝ → TrialResult E → Reply) (M delta rho deltaY : ℝ)
    (lam : ℝ → ℝ) (center : ℝ → E) (point : ℝ) :
    AllRequests (fun q : E × ℝ => q.2 = delta ∨ q.2 = deltaY)
      (mappedTaylorTrial classify M delta rho deltaY lam center point) :=
  allRequests_map _ _ _ (trialProgram_precision_set M (lam point) delta rho deltaY (center point))

end TaylorRequestPrecisions
end FangqingGetterComposition

namespace FangqingGetterComposition
open OriginalBetaATSTrial

theorem allRequests_mono {Q A R : Type*} (P S : Q → Prop)
    (hPS : ∀ q, P q → S q) (program : GetterProgram Q A R)
    (hp : AllRequests P program) : AllRequests S program := by
  induction program with
  | pure r => exact True.intro
  | ask q next ih => exact ⟨hPS q hp.1, fun a => ih a (hp.2 a)⟩

noncomputable def logarithmicAtomicBound (K eta : ℝ) : ℕ :=
  ⌈K * (1 + Real.log (1 + eta⁻¹))⌉₊

theorem logarithmicAtomicBound_antitone (K floor eta : ℝ)
    (hK : 0 ≤ K) (hfloor : 0 < floor) (heta : floor ≤ eta) :
    logarithmicAtomicBound K eta ≤ logarithmicAtomicBound K floor := by
  have hpos : 0 < eta := hfloor.trans_le heta
  have hinv : eta⁻¹ ≤ floor⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hfloor heta
  have hlog : Real.log (1 + eta⁻¹) ≤ Real.log (1 + floor⁻¹) :=
    Real.log_le_log (by positivity) (by linarith only [hinv])
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (by linarith only [hlog]) hK)

theorem logarithmic_baseCost_bound {Q A R : Type*}
    (getter : Q → A) (cost : Q → ℕ) (accuracy : Q → ℝ)
    (program : GetterProgram Q A R) (K floor : ℝ)
    (hK : 0 ≤ K) (hfloor : 0 < floor)
    (hprecision : ∀ q ∈ trace getter program, floor ≤ accuracy q)
    (hatomic : ∀ q : Q, 0 < accuracy q → cost q ≤ logarithmicAtomicBound K (accuracy q)) :
    baseCost getter cost program ≤ logarithmicAtomicBound K floor * (execute getter program).2 := by
  apply baseCost_le_mul_count
  intro q hq
  exact (hatomic q (hfloor.trans_le (hprecision q hq))).trans
    (logarithmicAtomicBound_antitone K floor (accuracy q) hK hfloor (hprecision q hq))

end FangqingGetterComposition
end

section
-- Source component: GetterProgramLowering.lean

namespace FangqingGetterComposition
open OriginalBetaATSTrial

noncomputable def primitiveLower {Q A BQ BA R : Type*}
    (oracle : Q → GetterProgram BQ BA A) : GetterProgram Q A R → GetterProgram BQ BA R
  | .pure r => .pure r
  | .ask q next => bind (oracle q) (fun a => primitiveLower oracle (next a))

noncomputable def implementedGetter {Q A BQ BA : Type*}
    (baseAnswer : BQ → BA) (oracle : Q → GetterProgram BQ BA A) (q : Q) : A :=
  (execute baseAnswer (oracle q)).1

noncomputable def implementedCost {Q A BQ BA : Type*}
    (baseAnswer : BQ → BA) (oracle : Q → GetterProgram BQ BA A) (q : Q) : ℕ :=
  (execute baseAnswer (oracle q)).2

theorem primitiveLower_execution {Q A BQ BA R : Type*}
    (baseAnswer : BQ → BA) (oracle : Q → GetterProgram BQ BA A)
    (program : GetterProgram Q A R) :
    execute baseAnswer (primitiveLower oracle program) =
      ((execute (implementedGetter baseAnswer oracle) program).1,
        baseCost (implementedGetter baseAnswer oracle) (implementedCost baseAnswer oracle) program) := by
  induction program with
  | pure r => rfl
  | ask q next ih =>
    simp only [primitiveLower, execute_bind, ih, execute, baseCost, implementedGetter, implementedCost]

end FangqingGetterComposition

namespace FangqingGetterComposition

theorem logarithmicAtomicBound_real_le (K eta : ℝ) (hK : 0 ≤ K) (heta : 0 < eta) :
    (logarithmicAtomicBound K eta : ℝ) ≤ K * (1 + Real.log (1 + eta⁻¹)) + 1 := by
  have hlog : 0 ≤ Real.log (1 + eta⁻¹) := Real.log_nonneg (by have h := inv_nonneg.mpr heta.le; linarith only [h])
  exact (Nat.ceil_lt_add_one (mul_nonneg hK (by linarith only [hlog]))).le

end FangqingGetterComposition
end

section
-- Source component: CoupledGetterProgram.lean

namespace OriginalCoupledGetterProgram

open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledBetaAlgebra
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def initialBound (c : Settings) (x y : E) (a : Answer E) : ℝ :=
  ‖a.grad‖ + 1 + c.Lg * ‖x - y‖

noncomputable def trials (c : Settings) (G deltaY : ℝ) (x y : E) :
    ℝ → GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Decision (Result E)) :=
  mappedTaylorTrial (classifyResult c) c.M (tolerance c G) c.rho deltaY
    (lambda c.A) (center x y)

noncomputable def positiveProgram (c : Settings) (deltaY : ℝ) (x y : E) :
    GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Outcome (Result E)) :=
  withInitial (y, 1) (fun a => trials c (initialBound c x y a) deltaY x y)
    (fun a => searchProgram c (initialBound c x y a) x y)

theorem trials_derivedReply (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (x y : E) :
    derivedReply getter (trials c G deltaY x y) = classifiedTrial getter c G deltaY x y := by
  funext b
  simp only [derivedReply, trials, mappedTaylorTrial, execute_map]
  rfl

theorem positiveProgram_result_and_count (getter : E × ℝ → Answer E) (c : Settings)
    (deltaY : ℝ) (x y : E) :
    (execute getter (positiveProgram c deltaY x y)).1 =
      (FangqingHysteresis.execute
        (classifiedTrial getter c (observedGradientBound getter c x y) deltaY x y)
        (searchProgram c (observedGradientBound getter c x y) x y)).1 ∧
    (execute getter (positiveProgram c deltaY x y)).2 ≤
      1 + 2 * (FangqingHysteresis.execute
        (classifiedTrial getter c (observedGradientBound getter c x y) deltaY x y)
        (searchProgram c (observedGradientBound getter c x y) x y)).2 := by
  have h := withInitial_result_and_count getter (y, 1)
    (fun a => trials c (initialBound c x y a) deltaY x y)
    (fun a => searchProgram c (initialBound c x y a) x y) 2
    (fun a b => mappedTaylorTrial_calls getter (classifyResult c) c.M
      (tolerance c (initialBound c x y a)) c.rho deltaY (lambda c.A) (center x y) b)
  rw [trials_derivedReply] at h
  exact h

theorem positiveProgram_success_and_getter_calls
    (g : E → ℝ) (c : Settings) (hc : Legal c) (deltaY : ℝ)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∃ value : Result E,
      (execute getter (positiveProgram c deltaY x y)).1 = .found value ∧
      ValidResult g c (observedGradientBound getter c x y) deltaY x y value ∧
      (execute getter (positiveProgram c deltaY x y)).2 ≤
        2 * fuel c (observedGradientBound getter c x y) x y + 5 := by
  have hbound := observed_bound_is_valid g c hc getter hgetter x y
  obtain ⟨value, hrun, hvalid, hcount⟩ := positive_search_success_and_calls g c hc
    (observedGradientBound getter c x y) deltaY hbound.1 hdeltaY hdeltaYsmall
    hC2 hsc hlip hHlip getter hgetter x y hbound.2
  have hprogram := positiveProgram_result_and_count getter c deltaY x y
  exact ⟨value, hprogram.1.trans hrun, hvalid, by omega⟩

theorem positiveProgram_getter_log_bound
    (getter : E × ℝ → Answer E) (c : Settings) (deltaY : ℝ) (x y : E)
    (hcount : (execute getter (positiveProgram c deltaY x y)).2 ≤
      2 * fuel c (observedGradientBound getter c x y) x y + 5) :
    ((execute getter (positiveProgram c deltaY x y)).2 : ℝ) ≤
      7 + 2 * Real.logb 2 (max 1
        ((modulus c (observedGradientBound getter c x y) x y *
          (upper c - lower c (observedGradientBound getter c x y))) /
            ((thresholdHigh c - thresholdLow c) / 2))) := by
  have h := positive_search_log_bound c (observedGradientBound getter c x y) x y
  have hnat : ((execute getter (positiveProgram c deltaY x y)).2 : ℝ) ≤
      2 * (fuel c (observedGradientBound getter c x y) x y : ℝ) + 5 := by exact_mod_cast hcount
  linarith only [h, hnat]

end OriginalCoupledGetterProgram

namespace OriginalCoupledGetterProgram
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledBetaAlgebra
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def precisionFloor (c : Settings) (G deltaY : ℝ) : ℝ :=
  min 1 (min (tolerance c G) deltaY)

theorem precisionFloor_positive (c : Settings) (hc : Legal c) (G deltaY : ℝ)
    (hG : 0 ≤ G) (hdeltaY : 0 < deltaY) : 0 < precisionFloor c G deltaY := by
  have hp := compact_properties c hc G hG
  have ht := OriginalBetaATSUniform.uniformTolerance_positive c.mu c.Lg c.M
    (lambdaMin c G) (lambdaMax c) c.sigma c.rho hc.mu_pos hc.Lg_nonneg
    hc.M_pos.le hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2 hc.sigma_pos hc.rho_pos
  exact lt_min (by norm_num) (lt_min ht hdeltaY)

theorem positiveProgram_request_precision_floor
    (getter : E × ℝ → Answer E) (c : Settings) (deltaY : ℝ) (x y : E) :
    ∀ q ∈ trace getter (positiveProgram c deltaY x y),
      precisionFloor c (observedGradientBound getter c x y) deltaY ≤ q.2 := by
  apply trace_withInitial_requests getter (y, 1)
    (fun a => trials c (initialBound c x y a) deltaY x y)
    (fun a => searchProgram c (initialBound c x y a) x y)
    (fun q : E × ℝ => precisionFloor c (observedGradientBound getter c x y) deltaY ≤ q.2)
  · exact min_le_left _ _
  · intro b
    apply allRequests_mono
      (fun q : E × ℝ => q.2 = tolerance c (observedGradientBound getter c x y) ∨ q.2 = deltaY)
    · intro q hq
      rcases hq with hq | hq
      · rw [hq]
        exact (min_le_right _ _).trans (min_le_left _ _)
      · rw [hq]
        exact (min_le_right _ _).trans (min_le_right _ _)
    · exact mappedTaylorTrial_precision_set (classifyResult c) c.M
        (tolerance c (observedGradientBound getter c x y)) c.rho deltaY (lambda c.A) (center x y) b

theorem positiveProgram_logarithmic_base_cost
    (getter : E × ℝ → Answer E) (cost : E × ℝ → ℕ) (c : Settings) (deltaY : ℝ) (x y : E)
    (K : ℝ) (hK : 0 ≤ K)
    (hfloor : 0 < precisionFloor c (observedGradientBound getter c x y) deltaY)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (hcount : (execute getter (positiveProgram c deltaY x y)).2 ≤
      2 * fuel c (observedGradientBound getter c x y) x y + 5) :
    baseCost getter cost (positiveProgram c deltaY x y) ≤
      logarithmicAtomicBound K (precisionFloor c (observedGradientBound getter c x y) deltaY) *
        (2 * fuel c (observedGradientBound getter c x y) x y + 5) := by
  exact (logarithmic_baseCost_bound getter cost Prod.snd (positiveProgram c deltaY x y) K _ hK hfloor
    (positiveProgram_request_precision_floor getter c deltaY x y) hatomic).trans
      (Nat.mul_le_mul_left _ hcount)

end OriginalCoupledGetterProgram
end

section
-- Source component: FirstCoupledStep.lean

namespace OriginalFirstCoupledStep

open OriginalCoupledBetaAlgebra
open OriginalCoupledBetaSearch
open OriginalBetaATSTrial (Answer)
open FangqingHysteresis (Decision Outcome)

structure CommonLegal (c : Settings) : Prop where
  mu_pos : 0 < c.mu
  Lg_nonneg : 0 ≤ c.Lg
  M_pos : 0 < c.M
  sigma_pos : 0 < c.sigma
  sigma_lt_one : c.sigma < 1
  low_pos : 0 < c.sigmaLow
  low_lt_up : c.sigmaLow < c.sigmaUp
  gap : c.sigmaLow * (1 + c.sigma) < c.sigmaUp * (1 - c.sigma)
  rho_pos : 0 < c.rho

noncomputable def proxySettings (c : Settings) : Settings := {c with A := 1}

theorem proxy_legal (c : Settings) (hc : CommonLegal c) : Legal (proxySettings c) :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hc.M_pos, by norm_num [proxySettings], hc.sigma_pos,
    hc.sigma_lt_one, hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

theorem positive_legal (c : Settings) (hc : CommonLegal c) (hA : 0 < c.A) : Legal c :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hc.M_pos, hA, hc.sigma_pos,
    hc.sigma_lt_one, hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem center_same (z : E) (b : ℝ) : center z z b = z := by dsimp [center]; module

noncomputable def fixedSearchProgram (c : Settings) (G : ℝ) (z : E) :
    FangqingHysteresis.Program (Decision (Result E)) (Outcome (Result E)) :=
  searchProgram (proxySettings c) G z z

noncomputable def fixedTrial (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (z : E) : ℝ → Decision (Result E) :=
  classifiedTrial getter (proxySettings c) G deltaY z z

def FixedValidResult (g : E → ℝ) (c : Settings) (deltaY : ℝ) (z : E) : Result E → Prop
  | .stop w => ‖gradient g w‖ ≤ c.rho
  | .window b d aY =>
      0 < b ∧ b < 1 ∧ 0 < lambda 1 b ∧
      c.sigmaLow / c.M ≤ lambda 1 b * ‖d‖ ∧ lambda 1 b * ‖d‖ ≤ c.sigmaUp / c.M ∧
      ‖lambda 1 b • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) c.M d + d‖ ≤ c.sigma * ‖d‖ ∧
      ‖aY.grad - gradient g (z + d)‖ ≤ deltaY ∧
      (lambda 1 b + Real.sqrt (lambda 1 b ^ 2 + 4 * lambda 1 b * 0)) / 2 = lambda 1 b ∧
      (0 / (0 + lambda 1 b)) • z + (lambda 1 b / (0 + lambda 1 b)) • z = z ∧
      0 < 0 + lambda 1 b

theorem proxy_result_is_actual_first_step
    (g : E → ℝ) (c : Settings) (deltaY G : ℝ) (z : E) (value : Result E)
    (hvalid : ValidResult g (proxySettings c) G deltaY z z value) :
    FixedValidResult g c deltaY z value := by
  cases value with
  | stop w => exact hvalid
  | window b d aY =>
    rcases hvalid with ⟨hb, hb0, hb1, hlam, hlow, hhigh, hATS, herr, hweight, hcenter⟩
    rw [center_same] at hATS herr
    have hzero := zero_weight_first_step (lambda 1 b) hlam z z
    exact ⟨hb0, hb1, hlam, hlow, hhigh, hATS, herr, hzero.1, hzero.2, by simpa only [zero_add, proxySettings] using hlam⟩

theorem first_step_success_and_calls
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ c.Lg * ‖x - y‖)
    (hHlip : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ c.M * ‖x - y‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ x : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (x, eta)).grad - gradient g x‖ ≤ eta ∧
      ‖(getter (x, eta)).hess - fderiv ℝ (gradient g) x‖ ≤ eta)
    (z : E) (hG : ‖gradient g z‖ ≤ G) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (fixedTrial getter c G deltaY z) (fixedSearchProgram c G z)).1 = .found value ∧
      FixedValidResult g c deltaY z value ∧
      (FangqingHysteresis.execute (fixedTrial getter c G deltaY z) (fixedSearchProgram c G z)).2 ≤
        fuel (proxySettings c) G z z + 2 := by
  have hG' : OriginalBetaCurveBounds.gradientBound g (proxySettings c).Lg z z ≤ G := by
    simpa only [OriginalBetaCurveBounds.gradientBound, sub_self, norm_zero, mul_zero, add_zero] using hG
  obtain ⟨value, hrun, hvalid, hcount⟩ := positive_search_success_and_calls g (proxySettings c)
    (proxy_legal c hc) G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip hHlip getter hgetter z z hG'
  exact ⟨value, hrun, proxy_result_is_actual_first_step g c deltaY G z value hvalid, hcount⟩

theorem first_step_log_bound (c : Settings) (G : ℝ) (z : E) :
    (fuel (proxySettings c) G z z : ℝ) + 2 ≤
      3 + Real.logb 2 (max 1 (((modulus (proxySettings c) G z z) *
        (upper (proxySettings c) - lower (proxySettings c) G)) /
          ((thresholdHigh (proxySettings c) - thresholdLow (proxySettings c)) / 2))) :=
  positive_search_log_bound (proxySettings c) G z z

end OriginalFirstCoupledStep
end

section
-- Source component: ZeroCurvatureSearch.lean

namespace OriginalZeroCurvatureSearch

open OriginalTaylorProxStability
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints
open OriginalBetaATSUniform
open OriginalBetaATSTrial (Answer TrialResult)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem zero_hessian_lipschitz_exact_taylor
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (z d : E) :
    CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) 0 d = gradient g (z + d) := by
  have hrem : ‖gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d‖ ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro e he
    let m := 2 * e / (‖d‖ ^ 2 + 1)
    have hm : 0 < m := by dsimp [m]; positivity
    have hHm : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ m * ‖x - y‖ := by
      intro x y
      have hh := hH0 x y
      simp only [zero_mul] at hh
      exact hh.trans (by positivity)
    have hb := RobustAHPE.gradient_taylor_remainder g hC2 m hm hHm z d
    calc
      _ ≤ m / 2 * ‖d‖ ^ 2 := hb
      _ ≤ 0 + e := by
        have heq : m / 2 * ‖d‖ ^ 2 = e * ‖d‖ ^ 2 / (‖d‖ ^ 2 + 1) := by dsimp [m]; ring
        rw [heq, zero_add]
        apply (div_le_iff₀ (by positivity : 0 < ‖d‖ ^ 2 + 1)).mpr
        nlinarith only [he]
  have hzero := norm_eq_zero.mp (le_antisymm hrem (norm_nonneg _))
  have heq : gradient g (z + d) = gradient g z + fderiv ℝ (gradient g) z d := by
    calc
      _ = (gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d) +
          (gradient g z + fderiv ℝ (gradient g) z d) := by abel
      _ = _ := by rw [hzero, zero_add]
  simpa only [CertifiedATS.trueVector, zero_div, zero_mul, zero_smul, add_zero] using heq.symm

noncomputable def largeLambda (mu sigma rho G : ℝ) : ℝ :=
  1 + 2 * ((1 + sigma) * G) / (mu * (1 - sigma) * rho)

theorem zero_curvature_large_lambda_small_gradient
    (g : E → ℝ) (mu lam sigma rho G : ℝ)
    (hmu : 0 < mu) (hlam : 0 < lam) (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1)
    (hrho : 0 < rho) (hG0 : 0 ≤ G) (hlarge : largeLambda mu sigma rho G ≤ lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (z d : E) (hG : ‖gradient g z‖ ≤ G)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) 0 d + d‖ ≤ sigma * ‖d‖) :
    ‖gradient g (z + d)‖ ≤ rho / 2 := by
  have hsize := exactStep_size_bound (gradient g z) (fderiv ℝ (gradient g) z) 0 lam mu
    (by norm_num) hlam hmu.le (CertifiedATS.actual_hessian_coercive g hC2 mu hsc z)
  have hRadius : ‖actualStep g 0 z lam‖ ≤ G / mu := by
    have hn : 0 ≤ lam⁻¹ * ‖actualStep g 0 z lam‖ := by positivity
    apply (le_div_iff₀ hmu).mpr
    change (mu + lam⁻¹) * ‖actualStep g 0 z lam‖ ≤ _ at hsize
    nlinarith only [hsize, hG, hn]
  have hbr := (actual_approximate_norm_bracket g mu 0 lam sigma hmu (by norm_num) hlam hC2 hsc z d hATS).1
  have hbr0 : (1 - sigma) * ‖d‖ ≤ ‖actualStep g 0 z lam‖ := by
    apply (mul_le_mul_iff_right₀ hlam).mp
    nlinarith only [hbr]
  have hmuDiv : mu * (G / mu) = G := by field_simp
  have hd : ‖d‖ ≤ G / (mu * (1 - sigma)) := by
    have hh := mul_le_mul_of_nonneg_left (hbr0.trans hRadius) hmu.le
    rw [hmuDiv] at hh
    apply (le_div_iff₀ (by positivity : 0 < mu * (1 - sigma))).mpr
    nlinarith only [hh]
  have hgradATS : ‖lam • gradient g (z + d) + d‖ ≤ sigma * ‖d‖ := by
    rwa [zero_hessian_lipschitz_exact_taylor g hC2 hH0 z d] at hATS
  have ht := norm_sub_le (lam • gradient g (z + d) + d) d
  have heq : (lam • gradient g (z + d) + d) - d = lam • gradient g (z + d) := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at ht
  have hgrad : ‖gradient g (z + d)‖ ≤ (1 + sigma) * (G / (mu * (1 - sigma))) / lam := by
    apply (le_div_iff₀ hlam).mpr
    have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 1 + sigma)
    nlinarith only [ht, hgradATS, hm]
  have hden : 0 < mu * (1 - sigma) * rho := by positivity
  have hl : 2 * ((1 + sigma) * G) / (mu * (1 - sigma) * rho) ≤ lam := by
    change 1 + _ ≤ lam at hlarge
    linarith only [hlarge]
  have hmul := (div_le_iff₀ hden).mp hl
  have hfinal : (1 + sigma) * (G / (mu * (1 - sigma))) / lam ≤ rho / 2 := by
    have heq' : (1 + sigma) * (G / (mu * (1 - sigma))) / lam =
        ((1 + sigma) * G) / (mu * (1 - sigma) * lam) := by field_simp <;> ring
    rw [heq']
    apply (div_le_iff₀ (by positivity : 0 < mu * (1 - sigma) * lam)).mpr
    nlinarith only [hmul]
  exact hgrad.trans hfinal

theorem zero_curvature_trial_stops
    (g : E → ℝ) (mu Lg lam sigma rho G deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hlam : 0 < lam) (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hrho : 0 < rho) (hG0 : 0 ≤ G) (hlarge : largeLambda mu sigma rho G ≤ lam)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (z : E) (hG : ‖gradient g z‖ ≤ G) :
    ∃ w : E, OriginalBetaATSTrial.trial getter 0 lam (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z = .stop w ∧
      ‖gradient g w‖ ≤ rho ∧
      (OriginalBetaATSTrial.execute getter
        (OriginalBetaATSTrial.trialProgram 0 lam (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z)).2 ≤ 2 := by
  have ht := OriginalBetaATSTrial.trial_uniform_spec g mu Lg 0 lam lam lam sigma rho deltaY
    hmu hLg (by norm_num) hlam le_rfl le_rfl hsigma0 hrho hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter z
  cases hout : OriginalBetaATSTrial.trial getter 0 lam (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z with
  | stop w =>
    rw [hout] at ht
    exact ⟨w, rfl, ht, OriginalBetaATSTrial.trial_getter_calls getter 0 lam _ rho deltaY z⟩
  | step d aY =>
    rw [hout] at ht
    have hg := zero_curvature_large_lambda_small_gradient g mu lam sigma rho G hmu hlam hsigma0.le hsigma1
      hrho hG0 hlarge hC2 hsc hH0 z d hG ht.1
    exact False.elim (not_lt_of_ge hg ht.2.2)


noncomputable def observedBound (getter : E × ℝ → Answer E) (Lg : ℝ) (x y : E) : ℝ :=
  ‖(getter (y, 1)).grad‖ + 1 + Lg * ‖x - y‖

noncomputable def chosenBeta (getter : E × ℝ → Answer E)
    (mu Lg A sigma rho : ℝ) (x y : E) : ℝ :=
  betaHigh A (largeLambda mu sigma rho (observedBound getter Lg x y))

theorem zero_curvature_observable_coupled_stop
    (g : E → ℝ) (mu Lg A sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hA : 0 < A)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    let b := chosenBeta getter mu Lg A sigma rho x y
    let lam := OriginalCoupledBetaAlgebra.lambda A b
    let z := OriginalCoupledBetaAlgebra.center x y b
    0 < b ∧ b < 1 ∧ 0 < lam ∧
    (∃ w : E, OriginalBetaATSTrial.trial getter 0 lam
      (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z = .stop w ∧
      ‖gradient g w‖ ≤ rho ∧
      (OriginalBetaATSTrial.execute getter
        (OriginalBetaATSTrial.trialProgram 0 lam
          (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z)).2 ≤ 2) := by
  let G := observedBound getter Lg x y
  have hG0 : 0 ≤ G := by dsimp [G, observedBound]; positivity
  have hG : gradientBound g Lg x y ≤ G :=
    gradient_upper_from_certificate g Lg x y _ 1 (hgetter y 1 (by norm_num)).1
  have hH0' : 0 ≤ largeLambda mu sigma rho G := by dsimp [largeLambda]; positivity
  have hb := betaHigh_properties A (largeLambda mu sigma rho G) hA hH0'
  have hb0 : 0 < betaHigh A (largeLambda mu sigma rho G) := by linarith only [hb.2.2.1]
  have hb1 := hb.2.2.2.1
  have hlam := (OriginalCoupledBetaAlgebra.coupled_weights A _ hA hb0 hb1).1
  refine ⟨hb0, hb1, hlam, ?_⟩
  apply zero_curvature_trial_stops g mu Lg _ sigma rho G deltaY hmu hLg hlam
    hsigma0 hsigma1 hrho hG0 hb.2.2.2.2 hdeltaY hdeltaYsmall hC2 hsc hlip hH0 getter hgetter
  exact (center_gradient_bound g Lg hLg hlip x y _ hb0.le hb1.le).trans hG

end OriginalZeroCurvatureSearch
end

section
-- Source component: Upper02DependencyExtract03.lean

namespace OriginalCoupledSearchComplete

open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def effectiveSettings (c : Settings) : Settings :=
  if 0 < c.A then c else proxySettings c

noncomputable def effectiveY (c : Settings) (x y : E) : E := if 0 < c.A then y else x

noncomputable def coupledProgram (c : Settings) (deltaY : ℝ) (x y : E) :=
  positiveProgram (effectiveSettings c) deltaY x (effectiveY c x y)

def ActualValid (g : E → ℝ) (c : Settings) (getter : E × ℝ → Answer E)
    (deltaY : ℝ) (x y : E) (value : Result E) : Prop :=
  if 0 < c.A then ValidResult g c (observedGradientBound getter c x y) deltaY x y value
  else FixedValidResult g c deltaY x value

theorem effective_legal (c : Settings) (hc : CommonLegal c) : Legal (effectiveSettings c) := by
  by_cases hA : 0 < c.A
  · simpa only [effectiveSettings, if_pos hA] using positive_legal c hc hA
  · simpa only [effectiveSettings, if_neg hA] using proxy_legal c hc

theorem effective_fields (c : Settings) :
    (effectiveSettings c).mu = c.mu ∧ (effectiveSettings c).Lg = c.Lg ∧
    (effectiveSettings c).M = c.M ∧ (effectiveSettings c).rho = c.rho := by
  by_cases hA : 0 < c.A <;> simp [effectiveSettings, hA, proxySettings]

theorem coupled_search_from_certified_getters
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (hA : 0 ≤ c.A)
    (deltaY : ℝ) (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    let e := effectiveSettings c
    let y' := effectiveY c x y
    let G := observedGradientBound getter e x y'
    ∃ value : Result E,
      (execute getter (coupledProgram c deltaY x y)).1 = .found value ∧
      ActualValid g c getter deltaY x y value ∧
      (0 < c.A ∨ c.A = 0) ∧
      (FangqingHysteresis.execute (classifiedTrial getter e G deltaY x y')
        (searchProgram e G x y')).2 ≤ fuel e G x y' + 2 ∧
      ((fuel e G x y' : ℕ) : ℝ) + 2 ≤
        3 + Real.logb 2 (max 1 ((modulus e G x y' * (upper e - lower e G)) /
          ((thresholdHigh e - thresholdLow e) / 2))) ∧
      (execute getter (coupledProgram c deltaY x y)).2 ≤ 2 * fuel e G x y' + 5 ∧
      0 < precisionFloor e G deltaY ∧
      (∀ q ∈ trace getter (coupledProgram c deltaY x y), precisionFloor e G deltaY ≤ q.2) ∧
      baseCost getter cost (coupledProgram c deltaY x y) ≤
        logarithmicAtomicBound K (precisionFloor e G deltaY) * (2 * fuel e G x y' + 5) := by
  let e := effectiveSettings c
  let y' := effectiveY c x y
  let G := observedGradientBound getter e x y'
  have he := effective_legal c hc
  have hf := effective_fields c
  have hde : deltaY ≤ e.rho / 8 := by simpa only [e, hf.2.2.2] using hdeltaYsmall
  have hsce : StrongConvexOn (Set.univ : Set E) e.mu g := by simpa only [e, hf.1] using hsc
  have hlipe : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ e.Lg * ‖z - w‖ := by
    simpa only [e, hf.2.1] using hlip
  have hHlipe : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ e.M * ‖z - w‖ := by
    simpa only [e, hf.2.2.1] using hHlip
  obtain ⟨value, hrun, hvalid, hcount⟩ := positiveProgram_success_and_getter_calls g e he deltaY
    hdeltaY hde hC2 hsce hlipe hHlipe getter hgetter x y'
  have hbound := observed_bound_is_valid g e he getter hgetter x y'
  obtain ⟨_, _, _, hATSCount⟩ := positive_search_success_and_calls g e he G deltaY hbound.1
    hdeltaY hde hC2 hsce hlipe hHlipe getter hgetter x y' hbound.2
  have hfloor := precisionFloor_positive e he G deltaY hbound.1 hdeltaY
  have hv : ActualValid g c getter deltaY x y value := by
    by_cases hpos : 0 < c.A
    · simpa only [ActualValid, if_pos hpos, e, effectiveSettings, y', effectiveY] using hvalid
    · apply (if_neg hpos).mpr
      apply proxy_result_is_actual_first_step g c deltaY G x value
      simpa only [G, e, effectiveSettings, y', effectiveY, if_neg hpos] using hvalid
  have hcases : 0 < c.A ∨ c.A = 0 := by
    by_cases hp : 0 < c.A
    · exact Or.inl hp
    · exact Or.inr (le_antisymm (le_of_not_gt hp) hA)
  exact ⟨value, hrun, hv, hcases, hATSCount, positive_search_log_bound e G x y', hcount,
    hfloor, positiveProgram_request_precision_floor getter e deltaY x y',
    positiveProgram_logarithmic_base_cost getter cost e deltaY x y' K hK hfloor hatomic hcount⟩

end OriginalCoupledSearchComplete
end

section
-- Source component: ZeroCurvatureProgram.lean

namespace OriginalZeroCurvatureSearch
open OriginalBetaATSTrial
open OriginalCoupledBetaAlgebra
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def initialBeta (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : ℝ :=
  OriginalBetaSearchEndpoints.betaHigh A (largeLambda mu sigma rho (‖a.grad‖ + 1 + Lg * ‖x - y‖))
noncomputable def initialLambda (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : ℝ :=
  lambda A (initialBeta mu Lg A sigma rho x y a)
noncomputable def initialCenter (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : E :=
  center x y (initialBeta mu Lg A sigma rho x y a)
noncomputable def initialTolerance (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : ℝ :=
  OriginalBetaATSUniform.uniformTolerance mu Lg 0
    (initialLambda mu Lg A sigma rho x y a) (initialLambda mu Lg A sigma rho x y a) sigma rho
noncomputable def zeroProgram (mu Lg A sigma rho deltaY : ℝ) (x y : E) :
    GetterProgram (E × ℝ) (Answer E) (TrialResult E) :=
  .ask (y, 1) (fun a => trialProgram 0 (initialLambda mu Lg A sigma rho x y a)
    (initialTolerance mu Lg A sigma rho x y a) rho deltaY (initialCenter mu Lg A sigma rho x y a))
noncomputable def zeroPrecisionFloor (getter : E × ℝ → Answer E)
    (mu Lg A sigma rho deltaY : ℝ) (x y : E) : ℝ :=
  min 1 (min (initialTolerance mu Lg A sigma rho x y (getter (y, 1))) deltaY)

theorem zeroProgram_trace_floor (getter : E × ℝ → Answer E)
    (mu Lg A sigma rho deltaY : ℝ) (x y : E) :
    ∀ q ∈ trace getter (zeroProgram mu Lg A sigma rho deltaY x y),
      zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y ≤ q.2 := by
  intro q hq
  simp only [zeroProgram, trace, List.mem_cons] at hq
  rcases hq with rfl | htail
  · exact min_le_left _ _
  · apply allRequests_trace getter
      (fun q : E × ℝ => zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y ≤ q.2)
      _ _ q htail
    apply allRequests_mono _ _ _ _ (trialProgram_precision_set 0 _ _ rho deltaY _)
    intro r hr
    rcases hr with hr | hr
    · rw [hr]
      exact (min_le_right _ _).trans (min_le_left _ _)
    · rw [hr]
      exact (min_le_right _ _).trans (min_le_right _ _)

theorem zeroProgram_small_gradient_and_logarithmic_cost
    (g : E → ℝ) (mu Lg A sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hA : 0 < A)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    ∃ w : E, (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).1 = .stop w ∧
      ‖gradient g w‖ ≤ rho ∧
      (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).2 ≤ 3 ∧
      0 < zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y ∧
      baseCost getter cost (zeroProgram mu Lg A sigma rho deltaY x y) ≤
        3 * logarithmicAtomicBound K (zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y) := by
  obtain ⟨hb, hb1, hlam, w, hw, hgrad, hcalls⟩ := zero_curvature_observable_coupled_stop g mu Lg A sigma rho deltaY
    hmu hLg hA hsigma0 hsigma1 hrho hdeltaY hdeltaYsmall hC2 hsc hlip hH0 getter hgetter x y
  have hrun : (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).1 = .stop w := hw
  have hcount : (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).2 ≤ 3 := by
    change (execute getter (trialProgram 0 _ _ rho deltaY _)).2 + 1 ≤ 3
    exact Nat.add_le_add_right hcalls 1
  have hlam' : 0 < initialLambda mu Lg A sigma rho x y (getter (y, 1)) := hlam
  have ht : 0 < initialTolerance mu Lg A sigma rho x y (getter (y, 1)) := by
    exact OriginalBetaATSUniform.uniformTolerance_positive mu Lg 0 _ _ sigma rho
      hmu hLg (by norm_num) hlam' hlam' hsigma0 hrho
  have hfloor : 0 < zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y :=
    lt_min (by norm_num) (lt_min ht hdeltaY)
  have hcost := logarithmic_baseCost_bound getter cost Prod.snd
    (zeroProgram mu Lg A sigma rho deltaY x y) K _ hK hfloor
    (zeroProgram_trace_floor getter mu Lg A sigma rho deltaY x y) hatomic
  refine ⟨w, hrun, hgrad, hcount, hfloor, hcost.trans ?_⟩
  calc
    _ ≤ logarithmicAtomicBound K (zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y) * 3 :=
      Nat.mul_le_mul_left _ hcount
    _ = _ := Nat.mul_comm _ _

end OriginalZeroCurvatureSearch
end

section
-- Source component: CoupledSearchAllCurvatures.lean

namespace OriginalCoupledSearchComplete
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open OriginalZeroCurvatureSearch
open FangqingGetterComposition

structure NonnegativeLegal (c : Settings) : Prop where
  mu_pos : 0 < c.mu
  Lg_nonneg : 0 ≤ c.Lg
  M_nonneg : 0 ≤ c.M
  sigma_pos : 0 < c.sigma
  sigma_lt_one : c.sigma < 1
  low_pos : 0 < c.sigmaLow
  low_lt_up : c.sigmaLow < c.sigmaUp
  gap : c.sigmaLow * (1 + c.sigma) < c.sigmaUp * (1 - c.sigma)
  rho_pos : 0 < c.rho

theorem positive_common (c : Settings) (hc : NonnegativeLegal c) (hM : 0 < c.M) : CommonLegal c :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hM, hc.sigma_pos, hc.sigma_lt_one,
    hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def zeroAsOutcome : TrialResult E → FangqingHysteresis.Outcome (Result E)
  | .stop w => .found (.stop w)
  | .step _ _ => .bracket 0 1

noncomputable def allCurvatureProgram (c : Settings) (deltaY : ℝ) (x y : E) :
    GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Outcome (Result E)) :=
  if 0 < c.M then coupledProgram c deltaY x y
  else FangqingGetterComposition.map zeroAsOutcome
    (zeroProgram c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY x (effectiveY c x y))

noncomputable def allPrecisionFloor (getter : E × ℝ → Answer E)
    (c : Settings) (deltaY : ℝ) (x y : E) : ℝ :=
  if 0 < c.M then precisionFloor (effectiveSettings c)
    (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) deltaY
  else zeroPrecisionFloor getter c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY x (effectiveY c x y)

noncomputable def allGetterBudget (getter : E × ℝ → Answer E)
    (c : Settings) (x y : E) : ℕ :=
  if 0 < c.M then 2 * fuel (effectiveSettings c)
    (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) x (effectiveY c x y) + 5
  else 3

noncomputable def allATSCalls (getter : E × ℝ → Answer E)
    (c : Settings) (deltaY : ℝ) (x y : E) : ℕ :=
  if 0 < c.M then (FangqingHysteresis.execute
    (classifiedTrial getter (effectiveSettings c)
      (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) deltaY x (effectiveY c x y))
    (searchProgram (effectiveSettings c)
      (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) x (effectiveY c x y))).2
  else 1

noncomputable def allATSLogBound (getter : E × ℝ → Answer E)
    (c : Settings) (x y : E) : ℝ :=
  if 0 < c.M then 3 + Real.logb 2 (max 1
    ((modulus (effectiveSettings c) (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y))
      x (effectiveY c x y) * (upper (effectiveSettings c) -
        lower (effectiveSettings c) (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)))) /
      ((thresholdHigh (effectiveSettings c) - thresholdLow (effectiveSettings c)) / 2)))
  else 1

def AllValid (g : E → ℝ) (c : Settings) (getter : E × ℝ → Answer E)
    (deltaY : ℝ) (x y : E) (value : Result E) : Prop :=
  if 0 < c.M then ActualValid g c getter deltaY x y value
  else match value with
    | .stop w => ‖gradient g w‖ ≤ c.rho
    | .window _ _ _ => False

theorem baseCost_map_actual {Q A R S : Type*} (getter : Q → A) (cost : Q → ℕ)
    (f : R → S) (p : GetterProgram Q A R) :
    baseCost getter cost (FangqingGetterComposition.map f p) = baseCost getter cost p := by
  induction p with
  | pure r => rfl
  | ask q next ih =>
    change cost q + baseCost getter cost (FangqingGetterComposition.map f (next (getter q))) =
      cost q + baseCost getter cost (next (getter q))
    rw [ih]

theorem coupled_search_all_nonnegative_curvatures
    (g : E → ℝ) (c : Settings) (hc : NonnegativeLegal c) (hA : 0 ≤ c.A)
    (deltaY : ℝ) (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    ∃ value : Result E,
      (execute getter (allCurvatureProgram c deltaY x y)).1 = .found value ∧
      AllValid g c getter deltaY x y value ∧
      (allATSCalls getter c deltaY x y : ℝ) ≤ allATSLogBound getter c x y ∧
      (execute getter (allCurvatureProgram c deltaY x y)).2 ≤ allGetterBudget getter c x y ∧
      0 < allPrecisionFloor getter c deltaY x y ∧
      baseCost getter cost (allCurvatureProgram c deltaY x y) ≤
        logarithmicAtomicBound K (allPrecisionFloor getter c deltaY x y) * allGetterBudget getter c x y := by
  classical
  by_cases hM : 0 < c.M
  · obtain ⟨value, hrun, hvalid, _, hATS, hlog, hcount, hfloor, _, hcost⟩ :=
      coupled_search_from_certified_getters g c (positive_common c hc hM) hA deltaY hdeltaY hdeltaYsmall
        hC2 hsc hlip hHlip getter hgetter cost K hK hatomic x y
    have hreal := Nat.cast_le (α := ℝ).mpr hATS
    simp only [Nat.cast_add, Nat.cast_ofNat] at hreal
    have hb : (allATSCalls getter c deltaY x y : ℝ) ≤ allATSLogBound getter c x y := by
      simp only [allATSCalls, allATSLogBound, if_pos hM]
      exact hreal.trans hlog
    exact ⟨value, by simpa only [allCurvatureProgram, if_pos hM] using hrun,
      by simpa only [AllValid, if_pos hM] using hvalid, hb,
      by simpa only [allCurvatureProgram, allGetterBudget, if_pos hM] using hcount,
      by simpa only [allPrecisionFloor, if_pos hM] using hfloor,
      by simpa only [allCurvatureProgram, allPrecisionFloor, allGetterBudget, if_pos hM] using hcost⟩
  · have hM0 : c.M = 0 := le_antisymm (le_of_not_gt hM) hc.M_nonneg
    have hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖ := by
      simpa only [hM0] using hHlip
    have hAe : 0 < (effectiveSettings c).A := by
      by_cases hpos : 0 < c.A
      · simpa only [effectiveSettings, if_pos hpos] using hpos
      · simp only [effectiveSettings, if_neg hpos, proxySettings]; norm_num
    obtain ⟨w, hrun, hg, hcount, hfloor, hcost⟩ :=
      zeroProgram_small_gradient_and_logarithmic_cost g c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY
        hc.mu_pos hc.Lg_nonneg hAe hc.sigma_pos hc.sigma_lt_one hc.rho_pos hdeltaY hdeltaYsmall
        hC2 hsc hlip hH0 getter hgetter cost K hK hatomic x (effectiveY c x y)
    refine ⟨.stop w, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [allCurvatureProgram, if_neg hM, execute_map, hrun, zeroAsOutcome]
    · simpa only [AllValid, if_neg hM] using hg
    · simp only [allATSCalls, allATSLogBound, if_neg hM, Nat.cast_one, le_refl]
    · simpa only [allCurvatureProgram, allGetterBudget, if_neg hM, execute_map] using hcount
    · simpa only [allPrecisionFloor, if_neg hM] using hfloor
    · simpa only [allCurvatureProgram, allPrecisionFloor, allGetterBudget, if_neg hM,
        baseCost_map_actual, Nat.mul_comm] using hcost

end OriginalCoupledSearchComplete
end

section
-- Source component: TrialQueryGeometry.lean

namespace OriginalTrialQueryGeometry
open OriginalBetaATSTrial
open OriginalTaylorProxStability
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem observable_model_step_norm_bound
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu M lam delta G : ℝ)
    (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z : E) (a : Answer E) (hgrad : ‖a.grad - gradient g z‖ ≤ delta)
    (hhess : ‖a.hess - fderiv ℝ (gradient g) z‖ ≤ delta)
    (hdelta : delta ≤ mu / 4) (hG : ‖gradient g z‖ ≤ G) :
    ‖exactStep a.grad a.hess M lam‖ ≤ 2 * (G + delta) / mu := by
  have hcoer : ∀ d : E, mu / 2 * ‖d‖ ^ 2 ≤ inner ℝ (a.hess d) d := by
    intro d
    have hh := CertifiedATS.approximate_hessian_coercive g hC2 mu hsc z a.hess delta hhess hdelta d
    rw [CertifiedATS.sympart_same_quadratic] at hh
    have hn := sq_nonneg ‖d‖
    nlinarith only [hh, hn, hmu]
  have hsize := exactStep_size_bound a.grad a.hess M lam (mu / 2) hM hlam (by positivity) hcoer
  have ha : ‖a.grad‖ ≤ G + delta := by
    have ht := norm_le_norm_sub_add a.grad (gradient g z)
    linarith only [ht, hgrad, hG]
  have hn : 0 ≤ lam⁻¹ * ‖exactStep a.grad a.hess M lam‖ := by positivity
  apply (le_div_iff₀ hmu).mpr
  nlinarith only [hsize, ha, hn]

theorem trial_trace_query_points
    (getter : E × ℝ → Answer E) (M lam delta rho deltaY : ℝ) (z : E) :
    ∀ q ∈ trace getter (trialProgram M lam delta rho deltaY z),
      q.1 = z ∨ q.1 = z + exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam := by
  classical
  intro q hq
  by_cases hs : ‖(getter (z, delta)).grad‖ + delta ≤ rho
  · simp only [trialProgram, trace, hs, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hq
    exact Or.inl (congrArg Prod.fst hq)
  · let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
    by_cases hy : ‖(getter (z + d, deltaY)).grad‖ + deltaY ≤ rho
    · simp only [trialProgram, trace, hs, ↓reduceIte, d, hy, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with hq | hq
      · exact Or.inl (congrArg Prod.fst hq)
      · exact Or.inr (congrArg Prod.fst hq)
    · simp only [trialProgram, trace, hs, ↓reduceIte, d, hy, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with hq | hq
      · exact Or.inl (congrArg Prod.fst hq)
      · exact Or.inr (congrArg Prod.fst hq)

theorem actual_trial_query_distance_bound
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu M lam delta rho deltaY G Bz : ℝ)
    (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (getter : E × ℝ → Answer E) (z w : E)
    (hgrad : ‖(getter (z, delta)).grad - gradient g z‖ ≤ delta)
    (hhess : ‖(getter (z, delta)).hess - fderiv ℝ (gradient g) z‖ ≤ delta)
    (hdelta : delta ≤ mu / 4) (hG : ‖gradient g z‖ ≤ G) (hcenter : ‖z - w‖ ≤ Bz) :
    ∀ q ∈ trace getter (trialProgram M lam delta rho deltaY z),
      ‖q.1 - w‖ ≤ Bz + 2 * (G + delta) / mu := by
  let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
  have hd : ‖d‖ ≤ 2 * (G + delta) / mu :=
    observable_model_step_norm_bound g hC2 mu M lam delta G hmu hM hlam hsc z _ hgrad hhess hdelta hG
  have hb : 0 ≤ 2 * (G + delta) / mu := (norm_nonneg d).trans hd
  intro q hq
  rcases trial_trace_query_points getter M lam delta rho deltaY z q hq with heq | heq
  · rw [heq]
    exact hcenter.trans (le_add_of_nonneg_right hb)
  · rw [heq]
    have hsplit : z + d - w = (z - w) + d := by abel
    change ‖z + d - w‖ ≤ _
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hcenter hd)

end OriginalTrialQueryGeometry
end

section
-- Source component: CoupledQueryGeometry.lean

namespace OriginalCoupledQueryGeometry
open OriginalBetaATSTrial
open OriginalTaylorProxStability
open OriginalCoupledBetaAlgebra
open OriginalBetaCurveBounds
open OriginalCoupledBetaSearch
open OriginalCoupledGetterProgram
open OriginalTrialQueryGeometry
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def AllAsks {Reply R : Type*} (P : ℝ → Prop) : FangqingHysteresis.Program Reply R → Prop
  | .pure _ => True
  | .ask b next => P b ∧ ∀ reply, AllAsks P (next reply)

theorem bisect_allAsks_interval {R : Type*} (n : ℕ) (L U l r : ℝ)
    (hL : L ≤ l) (hlr : l ≤ r) (hU : r ≤ U) :
    AllAsks (fun b => b ∈ Set.Icc L U) (FangqingHysteresis.bisect (R := R) n l r) := by
  induction n generalizing l r with
  | zero => exact True.intro
  | succ n ih =>
    change ((l + r) / 2 ∈ Set.Icc L U) ∧ _
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    intro reply
    cases reply with
    | accept v => exact True.intro
    | low => exact ih _ _ (by linarith) (by linarith) hU
    | high => exact ih _ _ hL (by linarith) (by linarith)

theorem search_allAsks_interval (c : Settings) (G : ℝ) (x y : E)
    (hLU : lower c G ≤ upper c) :
    AllAsks (fun b => b ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c)) (searchProgram c G x y) := by
  change (lower c G ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c)) ∧ _
  refine ⟨⟨le_rfl, hLU⟩, ?_⟩
  intro left
  cases left with
  | accept v => exact True.intro
  | low | high =>
    change (upper c ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c)) ∧ _
    refine ⟨⟨hLU, le_rfl⟩, ?_⟩
    intro right
    cases right with
    | accept v => exact True.intro
    | low | high => exact bisect_allAsks_interval _ _ _ _ _ le_rfl hLU le_rfl

theorem trace_bind_actual {Q A R S : Type*} (getter : Q → A)
    (p : GetterProgram Q A R) (next : R → GetterProgram Q A S) :
    trace getter (bind p next) = trace getter p ++ trace getter (next (execute getter p).1) := by
  induction p with
  | pure r => rfl
  | ask q cont ih => simp only [FangqingGetterComposition.bind, trace, execute, ih, List.cons_append]

theorem trace_map_actual {Q A R S : Type*} (getter : Q → A)
    (f : R → S) (p : GetterProgram Q A R) : trace getter (FangqingGetterComposition.map f p) = trace getter p := by
  simp only [FangqingGetterComposition.map, trace_bind_actual, trace, List.append_nil]

theorem actual_lower_trace_on_domain {Q A Reply R : Type*}
    (getter : Q → A) (trials : ℝ → GetterProgram Q A Reply)
    (domain : ℝ → Prop) (P : Q → Prop)
    (p : FangqingHysteresis.Program Reply R) (hp : AllAsks domain p)
    (htrials : ∀ b, domain b → ∀ q ∈ trace getter (trials b), P q) :
    ∀ q ∈ trace getter (FangqingGetterComposition.lower trials p), P q := by
  induction p with
  | pure v => simp only [FangqingGetterComposition.lower, trace, List.not_mem_nil, false_implies, implies_true]
  | ask b next ih =>
    intro q hq
    rw [FangqingGetterComposition.lower, trace_bind_actual, List.mem_append] at hq
    rcases hq with hq | hq
    · exact htrials b hp.1 q hq
    · exact ih (execute getter (trials b)).1 (hp.2 _) q hq

noncomputable def queryRadius (c : Settings) (G : ℝ) (x y : E) : ℝ :=
  ‖x - y‖ + 2 * (G + c.mu / 4) / c.mu

theorem positiveProgram_actual_query_ball
    (g : E → ℝ) (c : Settings) (hc : Legal c) (deltaY : ℝ)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∀ q ∈ trace getter (positiveProgram c deltaY x y),
      ‖q.1 - y‖ ≤ queryRadius c (observedGradientBound getter c x y) x y := by
  let G := observedGradientBound getter c x y
  have hbound := observed_bound_is_valid g c hc getter hgetter x y
  have hp := compact_properties c hc G hbound.1
  have ht := precisionFloor_positive c hc G 1 hbound.1 (by norm_num)
  have htol : 0 < tolerance c G :=
    ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : tolerance c G ≤ c.mu / 4 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hG0 : 0 ≤ G := hbound.1
  have hR : 0 ≤ queryRadius c G x y := by
    dsimp [queryRadius]
    have hmu := hc.mu_pos
    positivity
  intro q hq
  change q ∈ trace getter (.ask (y, 1) (fun a =>
    FangqingGetterComposition.lower (trials c (initialBound c x y a) deltaY x y)
      (searchProgram c (initialBound c x y a) x y))) at hq
  simp only [trace, List.mem_cons] at hq
  rcases hq with rfl | hq
  · simpa only [sub_self, norm_zero] using hR
  · apply actual_lower_trace_on_domain getter (trials c G deltaY x y)
      (fun b => b ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c))
      (fun q : E × ℝ => ‖q.1 - y‖ ≤ queryRadius c G x y)
      (searchProgram c G x y)
      (search_allAsks_interval c G x y hp.2.2.2.2.2.2.1) _ q hq
    intro b hb r hr
    have hinterval := interval_lambda_bounds c hc G hbound.1 b hb
    have hcenter : ‖center x y b - y‖ ≤ ‖x - y‖ := by
      have heq : center x y b - y = b • (x - y) := by dsimp [center]; module
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hinterval.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hinterval.2.1.le
    have hG : ‖gradient g (center x y b)‖ ≤ G :=
      (center_gradient_bound g c.Lg hc.Lg_nonneg hlip x y b hinterval.1.le hinterval.2.1.le).trans hbound.2
    have herrors := hgetter (center x y b) (tolerance c G) htol
    have htrace : r ∈ trace getter (trialProgram c.M (lambda c.A b) (tolerance c G)
        c.rho deltaY (center x y b)) := by
      simpa only [trials, mappedTaylorTrial, trace_map_actual] using hr
    have hh := actual_trial_query_distance_bound g hC2 c.mu c.M (lambda c.A b) (tolerance c G)
      c.rho deltaY G ‖x - y‖ hc.mu_pos hc.M_pos.le hinterval.2.2.1 hsc getter
      (center x y b) y herrors.1 herrors.2 hsmall hG hcenter r htrace
    have hfrac : 2 * (G + tolerance c G) / c.mu ≤ 2 * (G + c.mu / 4) / c.mu :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hsmall) (by norm_num)) hc.mu_pos.le
    exact hh.trans (add_le_add le_rfl hfrac)

end OriginalCoupledQueryGeometry
end

section
-- Source component: ZeroQueryGeometry.lean

namespace OriginalZeroQueryGeometry
open OriginalBetaATSTrial
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints
open OriginalCoupledBetaAlgebra
open OriginalZeroCurvatureSearch
open OriginalTrialQueryGeometry
open OriginalCoupledQueryGeometry
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem zeroProgram_actual_query_ball
    (g : E → ℝ) (mu Lg A sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hA : 0 < A)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∀ q ∈ trace getter (zeroProgram mu Lg A sigma rho deltaY x y),
      ‖q.1 - y‖ ≤ ‖x - y‖ + 2 * (observedBound getter Lg x y + mu / 4) / mu := by
  let G := observedBound getter Lg x y
  let b := initialBeta mu Lg A sigma rho x y (getter (y, 1))
  let lam := initialLambda mu Lg A sigma rho x y (getter (y, 1))
  let delta := initialTolerance mu Lg A sigma rho x y (getter (y, 1))
  have hG0 : 0 ≤ G := by dsimp [G, observedBound]; positivity
  have hG : gradientBound g Lg x y ≤ G :=
    gradient_upper_from_certificate g Lg x y _ 1 (hgetter y 1 (by norm_num)).1
  have hH : 0 ≤ largeLambda mu sigma rho G := by dsimp [largeLambda]; positivity
  have hb := betaHigh_properties A (largeLambda mu sigma rho G) hA hH
  have hb0 : 0 < b := by change 0 < betaHigh A (largeLambda mu sigma rho G); linarith only [hb.2.2.1]
  have hb1 : b < 1 := hb.2.2.2.1
  have hlam : 0 < lam := (coupled_weights A b hA hb0 hb1).1
  have hd : 0 < delta := OriginalBetaATSUniform.uniformTolerance_positive mu Lg 0 lam lam sigma rho
    hmu hLg (by norm_num) hlam hlam hsigma hrho
  have hsmall : delta ≤ mu / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcenter : ‖center x y b - y‖ ≤ ‖x - y‖ := by
    have heq : center x y b - y = b • (x - y) := by dsimp [center]; module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
    exact mul_le_of_le_one_left (norm_nonneg _) hb1.le
  have hgrad : ‖gradient g (center x y b)‖ ≤ G :=
    (center_gradient_bound g Lg hLg hlip x y b hb0.le hb1.le).trans hG
  have herrors := hgetter (center x y b) delta hd
  have hR : 0 ≤ ‖x - y‖ + 2 * (G + mu / 4) / mu := by positivity
  intro q hq
  simp only [zeroProgram, trace, List.mem_cons] at hq
  rcases hq with rfl | hq
  · simpa only [sub_self, norm_zero] using hR
  · have hh := actual_trial_query_distance_bound g hC2 mu 0 lam delta rho deltaY G ‖x - y‖
      hmu (by norm_num) hlam hsc getter (center x y b) y herrors.1 herrors.2 hsmall hgrad hcenter q hq
    exact hh.trans (add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsmall) (by norm_num)) hmu.le))

end OriginalZeroQueryGeometry

namespace OriginalZeroQueryGeometry
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledSearchComplete
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open OriginalCoupledQueryGeometry
open FangqingGetterComposition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def allQueryRadius (getter : E × ℝ → Answer E) (c : Settings) (x y : E) : ℝ :=
  let y' := effectiveY c x y
  ‖x - y'‖ + 2 * (observedGradientBound getter (effectiveSettings c) x y' + c.mu / 4) / c.mu

theorem allProgram_actual_query_ball
    (g : E → ℝ) (c : Settings) (hc : NonnegativeLegal c) (deltaY : ℝ)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∀ q ∈ trace getter (allCurvatureProgram c deltaY x y),
      ‖q.1 - effectiveY c x y‖ ≤ allQueryRadius getter c x y := by
  classical
  have hf := effective_fields c
  by_cases hM : 0 < c.M
  · have he := effective_legal c (positive_common c hc hM)
    have hsce : StrongConvexOn (Set.univ : Set E) (effectiveSettings c).mu g := by
      simpa only [hf.1] using hsc
    have hlipe : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ (effectiveSettings c).Lg * ‖z - w‖ := by
      simpa only [hf.2.1] using hlip
    have hh := positiveProgram_actual_query_ball g (effectiveSettings c) he deltaY hC2 hsce hlipe getter hgetter
      x (effectiveY c x y)
    simpa only [allCurvatureProgram, if_pos hM, coupledProgram, queryRadius, allQueryRadius, hf.1] using hh
  · have hAe : 0 < (effectiveSettings c).A := by
      by_cases hpos : 0 < c.A
      · simpa only [effectiveSettings, if_pos hpos] using hpos
      · simp only [effectiveSettings, if_neg hpos, proxySettings]; norm_num
    have hh := zeroProgram_actual_query_ball g c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY
      hc.mu_pos hc.Lg_nonneg hAe hc.sigma_pos hc.sigma_lt_one hc.rho_pos hC2 hsc hlip getter hgetter
      x (effectiveY c x y)
    simpa only [allCurvatureProgram, if_neg hM, trace_map_actual, allQueryRadius,
      OriginalZeroCurvatureSearch.observedBound, observedGradientBound, hf.2.1] using hh

end OriginalZeroQueryGeometry
end

section
-- Source component: DualGetterImplementation.lean

namespace OriginalDualGetterImplementation
open OriginalSaddleImplicit
open OriginalDualCurvature
open OriginalDualResidualQueryBound
open OriginalBetaATSTrial
open FangqingGetterComposition

noncomputable def liftQuery {Q A R : Type*} : OriginalDualOracleProgram.QueryProgram Q A R → GetterProgram Q A R
  | .pure r => .pure r
  | .ask q next => .ask q (fun a => liftQuery (next a))

theorem execute_liftQuery {Q A R : Type*} (oracle : Q → A)
    (p : OriginalDualOracleProgram.QueryProgram Q A R) :
    OriginalBetaATSTrial.execute oracle (liftQuery p) = OriginalDualOracleProgram.execute oracle p := by
  induction p with
  | pure r => rfl
  | ask q next ih => simp only [liftQuery, OriginalBetaATSTrial.execute, OriginalDualOracleProgram.execute, ih]

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def accuracyRadius (L rho eta : ℝ) : ℝ := min 1 (eta / (1 + 3 * L + 4 * rho))

noncomputable def oracleProgram (L rho : ℝ) (x u0 : E) (q : F × ℝ) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Answer F) :=
  FangqingGetterComposition.map
    (fun s : OriginalDualOracleProgram.QueryState E F =>
      ⟨OriginalDualOracleProgram.gradientOutput s, OriginalDualOracleProgram.hessianOutput L s⟩)
    (liftQuery (OriginalDualOracleProgram.simulator L x q.1 u0 (accuracyRadius L rho q.2)))

noncomputable def actualGetter (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E) : F × ℝ → Answer F :=
  implementedGetter (OriginalDualOracleProgram.actualOracle J) (oracleProgram L rho x u0)
noncomputable def actualCost (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E) : F × ℝ → ℕ :=
  implementedCost (OriginalDualOracleProgram.actualOracle J) (oracleProgram L rho x u0)

theorem actual_getter_accuracy
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (x u0 : E) (y : F) (eta : ℝ) (heta : 0 < eta) :
    ‖(actualGetter J L rho x u0 (y, eta)).grad - gradient (psi J L x) y‖ ≤ eta ∧
    ‖(actualGetter J L rho x u0 (y, eta)).hess - fderiv ℝ (gradient (psi J L x)) y‖ ≤ eta := by
  have hh := OriginalDualOracleProgram.arbitrary_accuracy_simulation J L rho hL hrho hC2 hLip hHess x u0 y eta heta
  simpa only [actualGetter, implementedGetter, oracleProgram, execute_map, execute_liftQuery,
    accuracyRadius] using And.intro hh.2.2.1 hh.2.2.2.1

theorem actual_cost_is_original_bundled_queries
    (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E) (q : F × ℝ) :
    actualCost J L rho x u0 q =
      (OriginalDualOracleProgram.execute (OriginalDualOracleProgram.actualOracle J)
        (OriginalDualOracleProgram.simulator L x q.1 u0 (accuracyRadius L rho q.2))).2 := by
  simp only [actualCost, implementedCost, oracleProgram, execute_map, execute_liftQuery]

theorem accuracyRadius_positive (L rho eta : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho) (heta : 0 < eta) :
    0 < accuracyRadius L rho eta := by unfold accuracyRadius; positivity

theorem accuracyRadius_mono (L rho floor eta : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho) (hfloor : floor ≤ eta) :
    accuracyRadius L rho floor ≤ accuracyRadius L rho eta := by
  exact min_le_min le_rfl (div_le_div_of_nonneg_right hfloor (by positivity))

noncomputable def queryBallBudget (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E)
    (y0 : F) (B floor : ℝ) : ℕ :=
  Nat.ceil (2 + 18 * Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / accuracyRadius L rho floor))

theorem actual_cost_on_query_ball_with_precision_floor
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y y0 : F) (B floor eta : ℝ)
    (hfloor : 0 < floor) (hprecision : floor ≤ eta) (hball : ‖y - y0‖ ≤ B) :
    actualCost J L rho x u0 (y, eta) ≤ queryBallBudget J L rho x u0 y0 B floor := by
  have hf := accuracyRadius_positive L rho floor hL hrho hfloor
  have he := accuracyRadius_positive L rho eta hL hrho (hfloor.trans_le hprecision)
  have hb : 0 ≤ B := (norm_nonneg _).trans hball
  have hobs : 0 ≤ observedRadius J L x u0 y0 := by unfold observedRadius; positivity
  have hc := actual_simulator_cost_on_query_ball J L hL hLip x u0 y y0 B
    (accuracyRadius L rho eta) he hball
  rw [← actual_cost_is_original_bundled_queries J L rho x u0 (y, eta)] at hc
  have heFloor := accuracyRadius_mono L rho floor eta hL hrho hprecision
  have hfrac := div_le_div_of_nonneg_left (show 0 ≤ 3 * (observedRadius J L x u0 y0 + B) by positivity)
    hf heFloor
  have hlog : Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / accuracyRadius L rho eta) ≤
      Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / accuracyRadius L rho floor) :=
    Real.log_le_log (by positivity) (add_le_add le_rfl hfrac)
  apply (Nat.cast_le (α := ℝ)).mp
  exact (hc.trans (by linarith only [hlog])).trans (Nat.le_ceil _)

end OriginalDualGetterImplementation
end

section
-- Source component: ActualDualCoupledSearch.lean

namespace OriginalActualDualCoupledSearch
open OriginalSaddleImplicit
open OriginalDualCurvature
open OriginalDualGetterImplementation
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledSearchComplete
open OriginalZeroQueryGeometry
open OriginalCoupledQueryGeometry
open FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def actualOriginalProgram (L rho : ℝ) (proxCenter uInit : E)
    (c : Settings) (deltaY : ℝ) (X Y : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F))
      (FangqingHysteresis.Outcome (Result F)) :=
  primitiveLower (oracleProgram L rho proxCenter uInit) (allCurvatureProgram c deltaY X Y)

noncomputable def originalQueryBudget (J : Joint E F → ℝ) (L rho : ℝ) (proxCenter uInit : E)
    (c : Settings) (deltaY : ℝ) (X Y : F) : ℕ :=
  let getter := actualGetter J L rho proxCenter uInit
  queryBallBudget J L rho proxCenter uInit (effectiveY c X Y) (allQueryRadius getter c X Y)
    (allPrecisionFloor getter c deltaY X Y) * allGetterBudget getter c X Y

theorem coupled_search_with_actual_original_oracle
    (J : Joint E F → ℝ) (L mu rho : ℝ) (hL : 0 < L) (hmu : 0 < mu) (hrho : 0 ≤ rho)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hconcave : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu
      (fun y => J (WithLp.toLp 2 (u, y))))
    (proxCenter uInit : E) (c : Settings) (hc : NonnegativeLegal c) (hA : 0 ≤ c.A)
    (hmuField : c.mu = mu) (hLgField : c.Lg = 2 * L) (hMField : c.M = (4 * Real.sqrt 2) * rho)
    (deltaY : ℝ) (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (X Y : F) :
    let getter := actualGetter J L rho proxCenter uInit
    ∃ value : Result F,
      (OriginalBetaATSTrial.execute (OriginalDualOracleProgram.actualOracle J)
        (actualOriginalProgram L rho proxCenter uInit c deltaY X Y)).1 = .found value ∧
      AllValid (psi J L proxCenter) c getter deltaY X Y value ∧
      (allATSCalls getter c deltaY X Y : ℝ) ≤ allATSLogBound getter c X Y ∧
      0 < allPrecisionFloor getter c deltaY X Y ∧
      (OriginalBetaATSTrial.execute (OriginalDualOracleProgram.actualOracle J)
        (actualOriginalProgram L rho proxCenter uInit c deltaY X Y)).2 ≤
          originalQueryBudget J L rho proxCenter uInit c deltaY X Y := by
  let getter := actualGetter J L rho proxCenter uInit
  let p := allCurvatureProgram c deltaY X Y
  let floor := allPrecisionFloor getter c deltaY X Y
  let B := allQueryRadius getter c X Y
  let budget := queryBallBudget J L rho proxCenter uInit (effectiveY c X Y) B floor
  have hd := dual_curvature_from_standing_joint J L mu rho hL hmu hrho hC2 hLip hHess hconcave proxCenter
  have hgsc : StrongConvexOn (Set.univ : Set F) c.mu (psi J L proxCenter) := by
    simpa only [hmuField] using hd.2.2.2.2.2.1
  have hglip : ∀ z w : F, ‖gradient (psi J L proxCenter) z - gradient (psi J L proxCenter) w‖ ≤ c.Lg * ‖z - w‖ := by
    simpa only [hLgField] using hd.2.2.2.2.2.2
  have hgHess : ∀ z w : F,
      ‖fderiv ℝ (gradient (psi J L proxCenter)) z - fderiv ℝ (gradient (psi J L proxCenter)) w‖ ≤ c.M * ‖z - w‖ := by
    simpa only [hMField] using hd.2.2.2.2.1
  have hgetter : ∀ z : F, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient (psi J L proxCenter) z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient (psi J L proxCenter)) z‖ ≤ eta :=
    actual_getter_accuracy J L rho hL hrho hC2 hLip hHess proxCenter uInit
  obtain ⟨value, hrun, hvalid, hATS, hcount, hfloor, _⟩ :=
    coupled_search_all_nonnegative_curvatures (psi J L proxCenter) c hc hA deltaY hdeltaY hdeltaYsmall
      hd.1 hgsc hglip hgHess getter hgetter (fun _ => 0) 0 (by norm_num)
      (fun _ _ => Nat.zero_le _) X Y
  have hpoints := allProgram_actual_query_ball (psi J L proxCenter) c hc deltaY hd.1 hgsc hglip getter hgetter X Y
  have hprecisions : ∀ q ∈ trace getter p, floor ≤ q.2 := by
    by_cases hM : 0 < c.M
    · simpa only [p, floor, allCurvatureProgram, if_pos hM, coupledProgram, allPrecisionFloor] using
        OriginalCoupledGetterProgram.positiveProgram_request_precision_floor getter (effectiveSettings c) deltaY X (effectiveY c X Y)
    · simpa only [p, floor, allCurvatureProgram, if_neg hM, trace_map_actual, allPrecisionFloor] using
        OriginalZeroCurvatureSearch.zeroProgram_trace_floor getter c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY X (effectiveY c X Y)
  have hcost : baseCost getter (actualCost J L rho proxCenter uInit) p ≤ budget * (execute getter p).2 := by
    apply baseCost_le_mul_count
    intro q hq
    exact actual_cost_on_query_ball_with_precision_floor J L rho hL hrho hLip proxCenter uInit q.1
      (effectiveY c X Y) B floor q.2 hfloor (hprecisions q hq) (hpoints q hq)
  have hbase := primitiveLower_execution (OriginalDualOracleProgram.actualOracle J)
    (oracleProgram L rho proxCenter uInit) p
  have hbase' : execute (OriginalDualOracleProgram.actualOracle J)
      (actualOriginalProgram L rho proxCenter uInit c deltaY X Y) =
      ((execute getter p).1, baseCost getter (actualCost J L rho proxCenter uInit) p) := hbase
  refine ⟨value, ?_, hvalid, hATS, hfloor, ?_⟩
  · rw [hbase']
    exact hrun
  · rw [hbase']
    exact hcost.trans (Nat.mul_le_mul_left _ hcount)

end OriginalActualDualCoupledSearch
end

section
-- Source component: DualGetterResourceComposition.lean

namespace OriginalDualGetterResourceComposition
open OriginalSaddleImplicit
open OriginalDualGetterImplementation
open OriginalBetaATSTrial
open FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem actual_original_queries_from_realized_geometry {R : Type*}
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x uInit : E) (y0 : F) (B floor : ℝ) (hfloor : 0 < floor)
    (p : GetterProgram (F × ℝ) (Answer F) R)
    (hpoint : ∀ q ∈ trace (actualGetter J L rho x uInit) p, ‖q.1 - y0‖ ≤ B)
    (hprecision : ∀ q ∈ trace (actualGetter J L rho x uInit) p, floor ≤ q.2) :
    (execute (OriginalDualOracleProgram.actualOracle J)
      (primitiveLower (oracleProgram L rho x uInit) p)).2 ≤
      queryBallBudget J L rho x uInit y0 B floor * (execute (actualGetter J L rho x uInit) p).2 := by
  rw [primitiveLower_execution]
  apply baseCost_le_mul_count
  intro q hq
  exact actual_cost_on_query_ball_with_precision_floor J L rho hL hrho hLip x uInit q.1 y0
    B floor q.2 hfloor (hprecision q hq) (hpoint q hq)

theorem actual_original_queries_from_checked_getter_budget {R : Type*}
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x uInit : E) (y0 : F) (B floor : ℝ) (hfloor : 0 < floor)
    (p : GetterProgram (F × ℝ) (Answer F) R) (N : ℕ)
    (hpoint : ∀ q ∈ trace (actualGetter J L rho x uInit) p, ‖q.1 - y0‖ ≤ B)
    (hprecision : ∀ q ∈ trace (actualGetter J L rho x uInit) p, floor ≤ q.2)
    (hcount : (execute (actualGetter J L rho x uInit) p).2 ≤ N) :
    (execute (OriginalDualOracleProgram.actualOracle J)
      (primitiveLower (oracleProgram L rho x uInit) p)).2 ≤
      queryBallBudget J L rho x uInit y0 B floor * N :=
  (actual_original_queries_from_realized_geometry J L rho hL hrho hLip x uInit y0 B floor hfloor p
    hpoint hprecision).trans (Nat.mul_le_mul_left _ hcount)

theorem actual_original_program_result {R : Type*}
    (J : Joint E F → ℝ) (L rho : ℝ) (x uInit : E)
    (p : GetterProgram (F × ℝ) (Answer F) R) :
    (execute (OriginalDualOracleProgram.actualOracle J)
      (primitiveLower (oracleProgram L rho x uInit) p)).1 =
      (execute (actualGetter J L rho x uInit) p).1 := by
  rw [primitiveLower_execution]
  rfl

end OriginalDualGetterResourceComposition
end

section
-- Source component: DualSaddleMinimizer.lean

namespace OriginalDualMinimizer

open OriginalSaddleImplicit OriginalPrimalElimination OriginalDualCurvature
open OriginalSaddleTransfer

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem primal_at_actual_dual_saddle
    (J : Joint E F → ℝ) (L mu : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) :
    primal J L x (vStar (JointSliceRegularity.curry J) L x) =
      uStar (JointSliceRegularity.curry J) L x := by
  let f := JointSliceRegularity.curry J
  have hdiffX := JointSliceRegularity.differentiable_x_slice J hJ
  have hdiffY := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx : ∀ y : F, ∀ u u' : E,
      ‖gradient (fun t => f t y) u - gradient (fun t => f t y) u'‖ ≤ L * ‖u - u'‖ :=
    fun y u u' => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u u' y
  have hxy : ∀ u : E, ∀ y y' : F,
      ‖gradient (fun t => f t y) u - gradient (fun t => f t y') u‖ ≤ L * ‖y - y'‖ :=
    fun u y y' => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y y'
  apply ((primal_is_unique_minimizer J L hL hJ hLip x (vStar f L x)).2 (uStar f L x) ?_).symm
  intro u
  have hh := OriginalSaddleStability.fixed_dual_quadratic_growth f L mu hL hmu
    hdiffX hdiffY hsc hxx hxy x u
  change f (uStar f L x) (vStar f L x) + L * ‖uStar f L x - x‖ ^ 2 +
      L / 2 * ‖u - uStar f L x‖ ^ 2 ≤ f u (vStar f L x) + L * ‖u - x‖ ^ 2 at hh
  have hn : 0 ≤ L / 2 * ‖u - uStar f L x‖ ^ 2 := by positivity
  linarith only [hh, hn]

theorem actual_dual_saddle_minimizes
    (J : Joint E F → ℝ) (L mu : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) :
    ∀ y : F, psi J L x (vStar (JointSliceRegularity.curry J) L x) ≤ psi J L x y := by
  intro y
  let f := JointSliceRegularity.curry J
  let u := uStar f L x
  let v := vStar f L x
  have hprimal := primal_at_actual_dual_saddle J L mu hL hmu hJ hLip hsc x
  have hmin := (primal_is_unique_minimizer J L hL hJ hLip x y).1 u
  have hmax := yStar_maximizes f mu hmu hsc
    (JointSliceRegularity.differentiable_y_slice J hJ) u y
  change f u y ≤ f u v at hmax
  rw [psi_eq_value_at_primal J L hL hJ hLip, psi_eq_value_at_primal J L hL hJ hLip]
  simp only [graph, hprimal]
  change -(f u v + L * ‖u - x‖ ^ 2) ≤
    -(f (primal J L x y) y + L * ‖primal J L x y - x‖ ^ 2)
  linarith only [hmin, hmax]

end OriginalDualMinimizer
end

section
-- Source component: GradientEnlargement.lean

namespace FrozenAudit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

def EpsilonSubgradient (g : E → ℝ) (y v : E) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ w : E, g y + inner ℝ v (w - y) - ε ≤ g w

theorem strongConvex_support
    (g : E → ℝ) (μ : ℝ)
    (hsc : StrongConvexOn (Set.univ : Set E) μ g)
    (hdiff : Differentiable ℝ g) (y w : E) :
    g y + inner ℝ (gradient g y) (w - y) +
      μ / 2 * ‖w - y‖ ^ 2 ≤ g w := by
  let h : E → ℝ := fun z => g z - μ / 2 * ‖z‖ ^ 2
  have hc : ConvexOn ℝ (Set.univ : Set E) h :=
    strongConvexOn_iff_convex.mp hsc
  let a : ℝ → E := fun t => y + t • (w - y)
  have ha0 : a 0 = y := by simp [a]
  have ha1 : a 1 = w := by
    dsimp [a]
    simp only [one_smul]
    abel
  have hline : ConvexOn ℝ (Set.univ : Set ℝ)
      (fun t : ℝ => h (a t)) := by
    refine ⟨convex_univ, ?_⟩
    intro s hs t ht p q hp hq hpq
    have haff : a (p * s + q * t) = p • a s + q • a t := by
      calc
        a (p * s + q * t) =
            (p + q) • y + (p * s + q * t) • (w - y) := by
          simp only [a, hpq, one_smul]
        _ = p • a s + q • a t := by
          simp only [a, smul_add, add_smul, mul_smul]
          abel
    have hh := hc.2 (Set.mem_univ (a s)) (Set.mem_univ (a t)) hp hq hpq
    simpa only [smul_eq_mul, ← haff] using hh
  have hcurve : HasDerivAt a (w - y) (0 : ℝ) := by
    simpa only [a, one_smul, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).smul_const (w - y)).const_add y)
  have hgy : HasFDerivAt g (fderiv ℝ g y) (a 0) := by
    rw [ha0]
    exact (hdiff y).hasFDerivAt
  have hgcurve : HasDerivAt (fun t : ℝ => g (a t))
      (inner ℝ (gradient g y) (w - y)) 0 := by
    simpa only [Function.comp_def, inner_gradient_left] using
      (hgy.comp_hasDerivAt (0 : ℝ) hcurve)
  have hnormcurve : HasDerivAt (fun t : ℝ => ‖a t‖ ^ 2)
      (2 * inner ℝ y (w - y)) 0 := by
    simpa only [ha0] using hcurve.norm_sq
  have hder : HasDerivAt (fun t : ℝ => h (a t))
      (inner ℝ (gradient g y) (w - y) -
        μ / 2 * (2 * inner ℝ y (w - y))) 0 := by
    simpa only [h, Pi.sub_def] using
      (hgcurve.sub (hnormcurve.const_mul (μ / 2)))
  have htangent := hline.le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) hder
  have ht : inner ℝ (gradient g y) (w - y) -
      μ / 2 * (2 * inner ℝ y (w - y)) ≤
      (g w - μ / 2 * ‖w‖ ^ 2) -
        (g y - μ / 2 * ‖y‖ ^ 2) := by
    simpa only [slope_def_field, ha0, ha1, h, sub_zero, div_one]
      using htangent
  rw [inner_sub_right (𝕜 := ℝ) y w y,
    real_inner_self_eq_norm_sq] at ht
  rw [norm_sub_sq_real, real_inner_comm y w]
  nlinarith only [ht]

theorem gradient_enlargement
    (g : E → ℝ) (μ δ : ℝ) (y v : E)
    (hμ : 0 < μ) (hdiff : Differentiable ℝ g)
    (hsc : StrongConvexOn (Set.univ : Set E) μ g)
    (herror : ‖v - gradient g y‖ ≤ δ) :
    EpsilonSubgradient g y v (δ ^ 2 / (2 * μ)) := by
  constructor
  · positivity
  · intro w
    have hs := strongConvex_support g μ hsc hdiff y w
    have he : inner ℝ (v - gradient g y) (w - y) ≤ δ * ‖w - y‖ := by
      calc
        inner ℝ (v - gradient g y) (w - y) ≤
            ‖v - gradient g y‖ * ‖w - y‖ := real_inner_le_norm _ _
        _ ≤ δ * ‖w - y‖ :=
          mul_le_mul_of_nonneg_right herror (norm_nonneg _)
    rw [inner_sub_left] at he
    have hden : 0 < 2 * μ := by positivity
    have hcancel : (δ ^ 2 / (2 * μ)) * (2 * μ) = δ ^ 2 :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have hquad : δ * ‖w - y‖ ≤
        μ / 2 * ‖w - y‖ ^ 2 + δ ^ 2 / (2 * μ) := by
      apply (mul_le_mul_iff_right₀ hμ).mp
      nlinarith only [hcancel, sq_nonneg (μ * ‖w - y‖ - δ)]
    nlinarith only [hs, he, hquad]

end FrozenAudit
end
