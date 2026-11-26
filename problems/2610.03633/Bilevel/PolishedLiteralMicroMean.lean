import Bilevel.PolishedLiteralFormulas
import Bilevel.PolishedLiteralMicroAdjustable

/-! Identification of the actual meanBase u-slice with the literal micro
core at an active macro selector, and the source kappa chain rule. The upper
primitive `upperBase` is deliberately not substituted for the hyperobjective
base `meanBase`: their residual difference is mathematically essential. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiRecursive ChiBoundedChain ZeroChainPotential RadialWrapper
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
namespace Parameters
variable (P : Parameters (X:=X) (U:=U))

/-- At an active macro value, every other selected micro value and release
vanishes identically as a function of u. This is an equality of the actual
source functions, not an assumed partial-gradient identity. -/
theorem meanBase_u_slice (x : X) (i : Fin (P.macroNode.n+1))
    (hi : wrappedSelector P.macroNode i x≠0) (u : U) :
    P.meanBase (pack x u)=P.macroCarrier x+
      microAttached P.n P.L P.β P.receiver P.ν P.force P.macroNode.width
        (wrappedSelector P.macroNode i x) (wrappedResidual P.macroNode i x)
        P.radius (P.frames i) u := by
  classical
  have hinactive (j : Fin (P.macroNode.n+1)) (hji : j≠i) : wrappedSelector P.macroNode j x=0 := by
    by_contra hj
    exact hji (wrappedSelector_unique P.macroNode j i x hj hi)
  have hsum : (∑ j : Fin (P.macroNode.n+1),wrappedSelector P.macroNode j x*P.microCore j u)=
      wrappedSelector P.macroNode i x*P.microCore i u := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hinactive j hji,zero_mul]
    · simp
  have hrel : (∑ j : Fin (P.macroNode.n+1),wrappedResidual P.macroNode j x*P.microRelease j u)=
      wrappedResidual P.macroNode i x*P.microRelease i u := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [(wrapped_inactive P.macroNode j x (hinactive j hji)).1,zero_mul]
    · simp
  rw [meanBase]
  change P.macroCarrier x+bowl P.ν P.radius u+
    (∑ j,wrappedSelector P.macroNode j x*P.microCore j u)+
      (∑ j,wrappedResidual P.macroNode j x*P.microRelease j u)=_
  rw [hsum,hrel,microAttached_formula]
  simp only [microCore,microRelease,terminal,coordinates]
  ring

theorem meanBase_contDiff : ContDiff ℝ 3 P.meanBase := by
  have he : P.meanBase=fun z => P.upperBase z+P.selectedResidual z :=
    funext (fun z => (P.exact_cancellation z).symm)
  rw [he]
  exact P.upperBase_contDiff.add P.selectedResidual_contDiff

theorem meanBase_u_hasGradientAt (hR : 0<P.radius) (x : X) (i : Fin (P.macroNode.n+1))
    (hi : wrappedSelector P.macroNode i x≠0) (u : U) :
    HasGradientAt (fun v => P.meanBase (pack x v))
      (gradient (microAttached P.n P.L P.β P.receiver P.ν P.force P.macroNode.width
        (wrappedSelector P.macroNode i x) (wrappedResidual P.macroNode i x)
        P.radius (P.frames i)) u) u := by
  have hm := microAttached_hasGradientAt P.n P.L P.β P.receiver P.ν P.force P.macroNode.width
    (wrappedSelector P.macroNode i x) (wrappedResidual P.macroNode i x) P.radius hR (P.frames i) u
  have he : (fun v => P.meanBase (pack x v))=fun v => P.macroCarrier x+
      microAttached P.n P.L P.β P.receiver P.ν P.force P.macroNode.width
        (wrappedSelector P.macroNode i x) (wrappedResidual P.macroNode i x)
        P.radius (P.frames i) v := funext (P.meanBase_u_slice x i hi)
  rw [he]
  apply hasGradientAt_iff_hasFDerivAt.mpr
  simpa only [hm.gradient] using hm.hasFDerivAt.const_add (P.macroCarrier x)

theorem meanBase_u_gradient_eq (hR : 0<P.radius) (x : X) (i : Fin (P.macroNode.n+1))
    (hi : wrappedSelector P.macroNode i x≠0) (u : U) :
    gradient (fun v => P.meanBase (pack x v)) u=
      gradient (microAttached P.n P.L P.β P.receiver P.ν P.force P.macroNode.width
        (wrappedSelector P.macroNode i x) (wrappedResidual P.macroNode i x)
        P.radius (P.frames i)) u :=
  (P.meanBase_u_hasGradientAt hR x i hi u).gradient

omit [CompleteSpace U] in
/-- The macro residual coefficient bound required by the micro certificate
is derived from the actual literal residual and selector range. -/
theorem actual_residual_coefficient_bound (hL : 0≤P.L) (hmacro : P.macroNode.ell=P.L)
    (x : X) (i : Fin (P.macroNode.n+1)) :
    wrappedResidual P.macroNode i x≤0 ∧
      |wrappedResidual P.macroNode i x|≤(Real.exp 1*gaussianBound)*P.L*P.macroNode.width^2 := by
  have hell : 0≤P.macroNode.ell := by rw [hmacro];exact hL
  refine ⟨wrappedResidual_nonpos P.macroNode hell i x,?_⟩
  have hb := wrappedResidual_abs_bound P.macroNode hell i x
  have hw := (wrappedSelector_range P.macroNode i x).2
  have hm := mul_le_mul_of_nonneg_left hw
    (mul_nonneg gaussianBound_nonneg (mul_nonneg hell (sq_nonneg P.macroNode.width)))
  rw [hmacro] at hb hm
  nlinarith only [hb,hm]

/-- The source hyperobjective before identifying the exact response ratio. -/
def outerMean (κ : ℝ) (z : Joint X U) : ℝ := P.meanBase (pack z.fst (κ • z.snd))

theorem outerMean_contDiff (κ : ℝ) : ContDiff ℝ 3 (P.outerMean κ) := by
  have hx : ContDiff ℝ 3 (fun z : Joint X U => z.fst) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ X U).contDiff.fst
  have hu : ContDiff ℝ 3 (fun z : Joint X U => z.snd) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ X U).contDiff.snd
  exact P.meanBase_contDiff.comp
    ((packLinear (X:=X) (Y:=U)).contDiff.comp (hx.prodMk (hu.const_smul κ)))

theorem outerMean_u_gradient_norm (κ : ℝ) (x : X) (v : U) :
    ‖gradient (fun v => P.outerMean κ (pack x v)) v‖=
      |κ| * ‖gradient (fun u => P.meanBase (pack x u)) (κ • v)‖ := by
  have he : ContDiff ℝ 3 (fun u => pack x u) :=
    (packLinear (X:=X) (Y:=U)).contDiff.comp (contDiff_const.prodMk contDiff_id)
  exact gradient_norm_comp_smul _ ((P.meanBase_contDiff.comp he).differentiable (by norm_num)) κ v

end Parameters

/-- The norm of the actual x-slice gradient is no larger than the full
Euclidean joint gradient. No supplied equality of partial derivatives. -/
theorem joint_partial_x_norm_le {f : Joint X U → ℝ} (x : X) (u : U)
    (hf : DifferentiableAt ℝ f (pack x u)) :
    ‖gradient (fun y => f (pack y u)) x‖≤‖gradient f (pack x u)‖ := by
  have hg : HasGradientAt f (pack (gradient f (pack x u)).fst (gradient f (pack x u)).snd)
      (pack x u) := hf.hasGradientAt
  have hp := PrimitiveGeometry.partial_x hg
  rw [hp.gradient]
  exact WithLp.norm_fst_le (p:=2) X (gradient f (pack x u))

/-- The matching u-slice norm comparison in the same L2 product geometry. -/
theorem joint_partial_u_norm_le {f : Joint X U → ℝ} (x : X) (u : U)
    (hf : DifferentiableAt ℝ f (pack x u)) :
    ‖gradient (fun v => f (pack x v)) u‖≤‖gradient f (pack x u)‖ := by
  have hg : HasGradientAt f (pack (gradient f (pack x u)).fst (gradient f (pack x u)).snd)
      (pack x u) := hf.hasGradientAt
  have hp := PrimitiveGeometry.partial_y hg
  rw [hp.gradient]
  exact WithLp.norm_snd_le (p:=2) X (gradient f (pack x u))

namespace Parameters
variable (P : Parameters (X:=X) (U:=U))

theorem outerMean_x_norm_le (κ : ℝ) (x : X) (v : U) :
    ‖gradient (fun y => P.outerMean κ (pack y v)) x‖≤‖gradient (P.outerMean κ) (pack x v)‖ :=
  joint_partial_x_norm_le x v ((P.outerMean_contDiff κ).differentiable (by norm_num) _)

theorem outerMean_u_norm_le (κ : ℝ) (x : X) (v : U) :
    ‖gradient (fun y => P.outerMean κ (pack x y)) v‖≤‖gradient (P.outerMean κ) (pack x v)‖ :=
  joint_partial_u_norm_le x v ((P.outerMean_contDiff κ).differentiable (by norm_num) _)

theorem outerMean_x_fderiv_norm_le (κ : ℝ) (x : X) (v : U) :
    ‖fderiv ℝ (fun y => P.outerMean κ (pack y v)) x‖≤
      ‖gradient (P.outerMean κ) (pack x v)‖ := by
  rw [←GradientJetBounds.gradient_norm_eq]
  exact P.outerMean_x_norm_le κ x v

theorem outerMean_u_fderiv_norm_le (κ : ℝ) (x : X) (v : U) :
    ‖fderiv ℝ (fun y => P.outerMean κ (pack x y)) v‖≤
      ‖gradient (P.outerMean κ) (pack x v)‖ := by
  rw [←GradientJetBounds.gradient_norm_eq]
  exact P.outerMean_u_norm_le κ x v

/-- This identity connects the functional F(x,v)=meanBase(x,kappa*v) with
actual primitive substitution once kappa=L/mu. -/
theorem outerMean_eq_actual_hyperobjective (hL : P.L≠0) (x : X) (v : U) :
    P.outerMean (P.L/P.μ) (pack x v)=
      PolishedLiteralJointMean.upper P.data x v (PolishedLiteralJointMean.response P.data x v) :=
  (P.exact_hyperobjective hL x v).symm

/-- The source kappa amplification of an actual micro-slice barrier into
the full joint outer gradient. The norm comparison uses the L2 product. -/
theorem outerMean_gradient_amplification (κ : ℝ) (hκ : 0≤κ) (x : X) (v : U)
    {target : ℝ} (hmargin : target≤‖gradient (fun u => P.meanBase (pack x u)) (κ • v)‖) :
    κ*target≤‖gradient (P.outerMean κ) (pack x v)‖ := by
  have hm := mul_le_mul_of_nonneg_left hmargin hκ
  have he := P.outerMean_u_gradient_norm κ x v
  rw [abs_of_nonneg hκ] at he
  rw [←he] at hm
  exact hm.trans (P.outerMean_u_norm_le κ x v)

end Parameters

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U] in
/-- Actual literal mean certificate: the scalar residual bound, selector
range, active-index reduction, source floor, radial estimates and kappa
chain rule are all instantiated. Constants precede every dimension and
public budget. Zeta may be shrunk after A and Cu have been fixed. -/
theorem actual_mean_micro_certificate (wstar : ℝ) (hws : 0<wstar) :
    ∃ A Cu cu : ℝ,0<A ∧ 0<Cu ∧ 0<cu ∧
    ∀ ζ : ℝ,0<ζ → ζ≤1 → ζ≤wstar/20 →
    ∃ κ₀ : ℝ,4≤κ₀ ∧
    ∀ (F G : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
      (P : Parameters (X:=F) (U:=G)) (κ : ℝ),
      0<P.L → 0<P.macroNode.width → κ₀≤κ → P.macroNode.ell=P.L →
      P.β=P.macroNode.width/κ → P.ν=ζ*P.L → P.radius=Cu*P.macroNode.width/ζ →
      P.receiver=A → P.force=P.L*P.β → P.n=Nat.floor (ζ^6*κ^2)-1 →
      ∀ (x : F) (v : G) (i : Fin (P.macroNode.n+1)),wstar≤wrappedSelector P.macroNode i x →
      P.microRelease i (κ • v)<1 →
      cu*(P.L*P.macroNode.width)≤‖gradient (P.outerMean κ) (pack x v)‖ := by
  let Cr := Real.exp 1*gaussianBound
  have hCr : 0≤Cr := mul_nonneg (Real.exp_pos _).le gaussianBound_nonneg
  obtain ⟨A,Cu,hA,hCu,hcert⟩ := parametric_micro_endgame Cr wstar hCr hws
  let cu := min wstar 1/2
  have hcu : 0<cu := div_pos (lt_min hws zero_lt_one) (by norm_num)
  refine ⟨A,Cu,cu,hA,hCu,hcu,?_⟩
  intro ζ hζ hζ1 hζw
  obtain ⟨κ₀,hκ₀,hκscale,hend⟩ := hcert ζ hζ hζ1 hζw
  refine ⟨κ₀,hκ₀,?_⟩
  intro F G _ _ _ _ _ _ P κ hL hb hκ hmacro hβ hν hR hreceiver hforce hn x v i hi hQ
  have hκ0 : 0<κ := lt_of_lt_of_le (by norm_num : (0:ℝ)<4) (hκ₀.trans hκ)
  have hgeom := micro_floor_geometry hζ hζ1 (hκ₀.trans hκ) (hκscale.trans hκ)
  have hsize : Real.sqrt ((P.n:ℝ)+1)≤κ := by rw [hn];exact hgeom.2
  have hactive : wrappedSelector P.macroNode i x≠0 := ne_of_gt (hws.trans_le hi)
  have hwe := (wrappedSelector_range P.macroNode i x).2
  have hr := P.actual_residual_coefficient_bound hL.le hmacro x i
  have hactualQ : releaseGate
      (WrappedChain.coordinates P.n (Cu*P.macroNode.width/ζ) (P.frames i) (κ • v)
        (Fin.last P.n)/P.macroNode.width)<1 := by
    simpa only [Parameters.microRelease,Parameters.terminal,Parameters.coordinates,hR] using hQ
  have hm := hend P.n P.L P.macroNode.width κ
    (wrappedSelector P.macroNode i x) (wrappedResidual P.macroNode i x)
    hL hb hκ hsize hi hwe hr.1 hr.2 G (P.frames i) (κ • v) hactualQ
  have hRpos : 0<P.radius := by rw [hR];positivity
  have hpartial : cu*(P.L*(P.macroNode.width/κ))≤
      ‖gradient (fun u => P.meanBase (pack x u)) (κ • v)‖ := by
    rw [P.meanBase_u_gradient_eq hRpos x i hactive]
    simpa only [hreceiver,hν,hR,hforce,hβ,cu,div_mul_eq_mul_div] using hm
  have hfull := P.outerMean_gradient_amplification κ hκ0.le x v hpartial
  have heq : κ*(cu*(P.L*(P.macroNode.width/κ)))=cu*(P.L*P.macroNode.width) := by
    field_simp
  rw [heq] at hfull
  exact hfull

end Bilevel.PolishedLiteral
