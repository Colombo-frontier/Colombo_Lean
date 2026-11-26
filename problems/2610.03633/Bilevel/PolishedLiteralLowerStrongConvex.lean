import Bilevel.PolishedLiteralLowerBudgets

/-! Actual lower-variable Hessian coercivity on the source lower space
(u,s), derived by affine restriction of the proved global perturbation
budget. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped RealInnerProductSpace
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

omit [InnerProductSpace ℝ X] [CompleteSpace X]
  [InnerProductSpace ℝ U] [CompleteSpace U] in
@[simp] theorem packed_add (a c : X) (b d : U) : pack a b+pack c d=pack (a+c) (b+d) := rfl

omit [CompleteSpace X] [CompleteSpace U] in
@[simp] theorem joint_smul_fst (c : ℝ) (z : Joint X U) : (c • z).fst=c • z.fst := rfl
omit [CompleteSpace X] [CompleteSpace U] in
@[simp] theorem joint_smul_snd (c : ℝ) (z : Joint X U) : (c • z).snd=c • z.snd := rfl
omit [CompleteSpace X] [CompleteSpace U] in
@[simp] theorem fstMap_apply_literal (z : Joint X U) : fstMap z=z.fst := rfl
omit [CompleteSpace X] [CompleteSpace U] in
@[simp] theorem sndMap_apply_literal (z : Joint X U) : sndMap z=z.snd := rfl

def lowerInsert : Joint U ℝ →L[ℝ] FullMeanSpace (X:=X) (U:=U) :=
  (packLinear (X:=Joint X U) (Y:=Joint U ℝ)).comp
    ((0 : Joint U ℝ →L[ℝ] Joint X U).prod (ContinuousLinearMap.id ℝ (Joint U ℝ)))

omit [CompleteSpace X] [CompleteSpace U] in
theorem lowerInsert_apply (y : Joint U ℝ) : lowerInsert (X:=X) y=pack 0 y := rfl

omit [CompleteSpace X] [CompleteSpace U] in
theorem lowerInsert_norm : ‖lowerInsert (X:=X) (U:=U)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  rw [lowerInsert_apply]
  have h := norm_sq (pack (0:Joint X U) y)
  change ‖pack (0:Joint X U) y‖^2=‖(0:Joint X U)‖^2+‖y‖^2 at h
  simp only [norm_zero,zero_pow (by norm_num : 2≠0),zero_add] at h
  nlinarith [norm_nonneg (pack (0:Joint X U) y),norm_nonneg y]

namespace Parameters
variable (P : Parameters (X:=X) (U:=U))

def lowerPerturbationSlice (x : X) (y : Joint U ℝ) : ℝ :=
  PolishedLiteralJointMean.perturbation P.data x y

theorem lowerPerturbationSlice_contDiff (x : X) : ContDiff ℝ 3 (P.lowerPerturbationSlice x) := by
  let a : FullMeanSpace (X:=X) (U:=U) := pack (pack x 0) 0
  have he : P.lowerPerturbationSlice x=(fun q => P.sourcePerturbation (a+q)) ∘ lowerInsert := by
    funext y
    simp only [Function.comp_apply,a,lowerInsert_apply,packed_add,add_zero,zero_add,packed_fst,packed_snd,sourcePerturbation,lowerPerturbationSlice]
  rw [he]
  exact (P.sourcePerturbation_contDiff.comp (contDiff_const.add contDiff_id)).comp
    (lowerInsert (X:=X) (U:=U)).contDiff

theorem lowerPerturbationSlice_second (x : X)
    (hpert : ∀ z,‖iteratedFDeriv ℝ 2 P.data.perturbation z‖≤P.μ/2) (y : Joint U ℝ) :
    ‖iteratedFDeriv ℝ 2 (P.lowerPerturbationSlice x) y‖≤P.μ/2 := by
  let a : FullMeanSpace (X:=X) (U:=U) := pack (pack x 0) 0
  let f : FullMeanSpace (X:=X) (U:=U) → ℝ := fun q => P.sourcePerturbation (a+q)
  have hf : ContDiff ℝ 3 f := P.sourcePerturbation_contDiff.comp (contDiff_const.add contDiff_id)
  have he : P.lowerPerturbationSlice x=f ∘ lowerInsert := by
    funext y
    simp only [Function.comp_apply,f,a,lowerInsert_apply,packed_add,add_zero,zero_add,packed_fst,packed_snd,sourcePerturbation,lowerPerturbationSlice]
  rw [he]
  have ht := ChiOuter.contraction_jet_bound (lowerInsert (X:=X) (U:=U)) lowerInsert_norm hf y 2 (by norm_num)
  apply ht.trans
  change ‖iteratedFDeriv ℝ 2 f (lowerInsert y)‖≤P.μ/2
  rw [iteratedFDeriv_comp_add_left]
  exact (P.sourcePerturbation_jet_le (a+lowerInsert y) 2 (by norm_num)).trans (hpert _)

theorem lower_hasGradientAt (x : X) (v : U) (y : Joint U ℝ) :
    HasGradientAt (PolishedLiteralJointMean.lower P.data x v)
      (P.μ • y-pack (P.L • v) 0+gradient (P.lowerPerturbationSlice x) y) y := by
  have hu := (fstMap (X:=U) (U:=ℝ)).hasFDerivAt (x:=y)
  have hs := (sndMap (X:=U) (U:=ℝ)).hasFDerivAt (x:=y)
  have hk := ((P.lowerPerturbationSlice_contDiff x).differentiable (by norm_num) y).hasGradientAt.hasFDerivAt
  have h := ((((hu.inner ℝ hu).add (hs.mul hs)).const_mul (P.μ/2)).sub
    (((hasFDerivAt_const v y).inner ℝ hu).const_mul P.L)).add hk
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h using 1
  · funext t
    simp only [PolishedLiteralJointMean.lower,lowerPerturbationSlice,pow_two,
      real_inner_self_eq_norm_sq,Parameters.data,fstMap_apply_literal,sndMap_apply_literal]
  ext d
  simp only [InnerProductSpace.toDual_apply,inner_add_left,inner_sub_left,real_inner_smul_left,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,fderivInnerCLM_apply,
    smul_eq_mul,WithLp.prod_inner_apply,packed_fst,packed_snd,inner_zero_left,zero_add,
    joint_smul_fst,joint_smul_snd,fstMap_apply_literal,sndMap_apply_literal,real_inner_smul_left,
    ContinuousLinearMap.zero_apply,
    RCLike.inner_apply,conj_trivial,zero_mul,add_zero]
  rw [real_inner_comm d.fst y.fst]
  ring

theorem lowerYY_coercive (_hμ : 0<P.μ)
    (hpert : ∀ z,‖iteratedFDeriv ℝ 2 P.data.perturbation z‖≤P.μ/2)
    (x : X) (v : U) (y d : Joint U ℝ) :
    (P.μ/2)*‖d‖^2≤⟪(fderiv ℝ (gradient (PolishedLiteralJointMean.lower P.data x v)) y) d,d⟫ := by
  have hgrad : gradient (PolishedLiteralJointMean.lower P.data x v)=fun y =>
      P.μ • y-pack (P.L • v) 0+gradient (P.lowerPerturbationSlice x) y :=
    funext (fun y => (P.lower_hasGradientAt x v y).gradient)
  have hk := (GradientJetBounds.gradient_contDiff (P.lowerPerturbationSlice_contDiff x)).differentiable (by norm_num) y
  have hd := (((hasFDerivAt_id y).const_smul P.μ).sub_const (pack (P.L • v) (0:ℝ))).add hk.hasFDerivAt
  simp only [id_eq] at hd
  rw [hgrad,hd.fderiv]
  have hnorm : ‖fderiv ℝ (gradient (P.lowerPerturbationSlice x)) y‖≤P.μ/2 :=
    (GradientJetBounds.hessian_norm_eq (P.lowerPerturbationSlice_contDiff x) y).le.trans
      (P.lowerPerturbationSlice_second x hpert y)
  let H := fderiv ℝ (gradient (P.lowerPerturbationSlice x)) y
  have hv : ‖H d‖≤(P.μ/2)*‖d‖ := (H.le_opNorm d).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg d))
  have hi : |⟪H d,d⟫|≤(P.μ/2)*‖d‖^2 := (abs_real_inner_le_norm _ _).trans (by
    convert mul_le_mul_of_nonneg_right hv (norm_nonneg d) using 1;ring)
  change (P.μ/2)*‖d‖^2≤⟪P.μ • d+H d,d⟫
  rw [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
  nlinarith [(abs_le.mp hi).1]

end Parameters
end Bilevel.PolishedLiteral
