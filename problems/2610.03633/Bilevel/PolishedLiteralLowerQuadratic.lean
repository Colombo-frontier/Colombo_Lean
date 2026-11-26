import Bilevel.PolishedLiteralLowerGeometry

/-! The actual source quadratic in ((x,v),(u,s)). Its Hessian is a constant
symmetric operator; all third derivatives vanish. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

local instance : NormedAddCommGroup (FullMeanSpace (X:=X) (U:=U) →L[ℝ] FullMeanSpace (X:=X) (U:=U)) := inferInstance
local instance : NormedSpace ℝ (FullMeanSpace (X:=X) (U:=U) →L[ℝ] FullMeanSpace (X:=X) (U:=U)) := inferInstance

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U] in
@[simp] theorem packed_fst (a : X) (b : U) : (pack a b).fst=a := rfl
omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U] in
@[simp] theorem packed_snd (a : X) (b : U) : (pack a b).snd=b := rfl

def lowerProjection : FullMeanSpace (X:=X) (U:=U) →L[ℝ] FullMeanSpace (X:=X) (U:=U) :=
  (packLinear (X:=Joint X U) (Y:=Joint U ℝ)).comp
    ((0 : FullMeanSpace (X:=X) (U:=U) →L[ℝ] Joint X U).prod (sndMap (X:=Joint X U) (U:=Joint U ℝ)))

def lowerSwapOuter : FullMeanSpace (X:=X) (U:=U) →L[ℝ] Joint X U :=
  (packLinear (X:=X) (Y:=U)).comp
    ((0 : FullMeanSpace (X:=X) (U:=U) →L[ℝ] X).prod
      ((fstMap (X:=U) (U:=ℝ)).comp (sndMap (X:=Joint X U) (U:=Joint U ℝ))))

def lowerSwapInner : FullMeanSpace (X:=X) (U:=U) →L[ℝ] Joint U ℝ :=
  (packLinear (X:=U) (Y:=ℝ)).comp
    (((sndMap (X:=X) (U:=U)).comp (fstMap (X:=Joint X U) (U:=Joint U ℝ))).prod
      (0 : FullMeanSpace (X:=X) (U:=U) →L[ℝ] ℝ))

def lowerSwap : FullMeanSpace (X:=X) (U:=U) →L[ℝ] FullMeanSpace (X:=X) (U:=U) :=
  (packLinear (X:=Joint X U) (Y:=Joint U ℝ)).comp (lowerSwapOuter.prod lowerSwapInner)

omit [CompleteSpace X] [CompleteSpace U] in
theorem lowerProjection_apply (q : FullMeanSpace (X:=X) (U:=U)) : lowerProjection q=pack 0 q.snd := rfl

omit [CompleteSpace X] [CompleteSpace U] in
theorem lowerSwap_apply (q : FullMeanSpace (X:=X) (U:=U)) :
    lowerSwap q=pack (pack 0 q.snd.fst) (pack q.fst.snd 0) := rfl

omit [CompleteSpace X] [CompleteSpace U] in
theorem lowerProjection_norm : ‖lowerProjection (X:=X) (U:=U)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  rw [lowerProjection_apply]
  have h := norm_sq (pack (0:Joint X U) q.snd)
  have hq := norm_sq q
  change ‖pack (0:Joint X U) q.snd‖≤1*‖q‖
  change ‖pack (0:Joint X U) q.snd‖^2=‖(0:Joint X U)‖^2+‖q.snd‖^2 at h
  simp only [norm_zero,zero_pow (by norm_num : 2≠0),zero_add] at h
  nlinarith [norm_nonneg q,norm_nonneg (pack (0:Joint X U) q.snd),sq_nonneg ‖q.fst‖]

omit [CompleteSpace X] [CompleteSpace U] in
theorem lowerSwap_norm : ‖lowerSwap (X:=X) (U:=U)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  rw [lowerSwap_apply]
  have h := norm_sq (pack (pack (0:X) q.snd.fst) (pack q.fst.snd (0:ℝ)))
  have ho := norm_sq (pack (0:X) q.snd.fst)
  have hi := norm_sq (pack q.fst.snd (0:ℝ))
  have hq := norm_sq q
  have hqo := norm_sq q.fst
  have hqi := norm_sq q.snd
  change ‖pack (pack (0:X) q.snd.fst) (pack q.fst.snd (0:ℝ))‖^2=
    ‖pack (0:X) q.snd.fst‖^2+‖pack q.fst.snd (0:ℝ)‖^2 at h
  change ‖pack (0:X) q.snd.fst‖^2=‖(0:X)‖^2+‖q.snd.fst‖^2 at ho
  change ‖pack q.fst.snd (0:ℝ)‖^2=‖q.fst.snd‖^2+‖(0:ℝ)‖^2 at hi
  simp only [norm_zero,zero_pow (by norm_num : 2≠0),zero_add,add_zero] at ho hi
  nlinarith [norm_nonneg q,norm_nonneg (pack (pack (0:X) q.snd.fst) (pack q.fst.snd (0:ℝ))),
    sq_nonneg ‖q.fst.fst‖,sq_nonneg ‖q.snd.snd‖]

def lowerBaseHessian (μ L : ℝ) : FullMeanSpace (X:=X) (U:=U) →L[ℝ] FullMeanSpace (X:=X) (U:=U) :=
  μ • lowerProjection-L • lowerSwap

def lowerBase (μ L : ℝ) (q : FullMeanSpace (X:=X) (U:=U)) : ℝ :=
  μ/2*(‖q.snd.fst‖^2+q.snd.snd^2)-L*⟪q.fst.snd,q.snd.fst⟫

omit [CompleteSpace X] [CompleteSpace U] in
theorem lowerBaseHessian_symmetric (μ L : ℝ) (a b : FullMeanSpace (X:=X) (U:=U)) :
    ⟪lowerBaseHessian μ L a,b⟫=⟪a,lowerBaseHessian μ L b⟫ := by
  have hp : ⟪lowerProjection a,b⟫=⟪a,lowerProjection b⟫ := by
    simp only [lowerProjection_apply,WithLp.prod_inner_apply,packed_fst,packed_snd,inner_zero_left,inner_zero_right,zero_add,add_zero]
  have hs : ⟪lowerSwap a,b⟫=⟪a,lowerSwap b⟫ := by
    simp only [lowerSwap_apply,WithLp.prod_inner_apply,packed_fst,packed_snd,inner_zero_left,inner_zero_right,
      RCLike.inner_apply,conj_trivial,zero_mul,mul_zero,zero_add,add_zero]
    ring
  change ⟪μ • lowerProjection a-L • lowerSwap a,b⟫=⟪a,μ • lowerProjection b-L • lowerSwap b⟫
  rw [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_left,
    real_inner_smul_right,real_inner_smul_right,hp,hs]

omit [CompleteSpace X] [CompleteSpace U] in
theorem lowerBase_eq_quadratic (μ L : ℝ) (q : FullMeanSpace (X:=X) (U:=U)) :
    lowerBase μ L q=(1/2)*⟪lowerBaseHessian μ L q,q⟫ := by
  have hp : ⟪lowerProjection q,q⟫=‖q.snd‖^2 := by
    simp only [lowerProjection_apply,WithLp.prod_inner_apply,packed_fst,packed_snd,inner_zero_left,zero_add,real_inner_self_eq_norm_sq]
    exact (PrimitiveGeometry.norm_sq q.snd).symm
  have hs : ⟪lowerSwap q,q⟫=2*⟪q.fst.snd,q.snd.fst⟫ := by
    simp only [lowerSwap_apply,WithLp.prod_inner_apply,packed_fst,packed_snd,inner_zero_left,inner_zero_right,
      RCLike.inner_apply,conj_trivial,zero_mul,mul_zero,zero_add,add_zero]
    rw [real_inner_comm q.snd.fst q.fst.snd]
    ring
  change lowerBase μ L q=(1/2)*⟪μ • lowerProjection q-L • lowerSwap q,q⟫
  rw [inner_sub_left,real_inner_smul_left,real_inner_smul_left,hp,hs]
  have hy := PrimitiveGeometry.norm_sq q.snd
  simp only [Real.norm_eq_abs,sq_abs] at hy
  unfold lowerBase
  rw [hy]
  ring

omit [CompleteSpace X] [CompleteSpace U] in
theorem lowerBase_contDiff (μ L : ℝ) : ContDiff ℝ 3 (lowerBase (X:=X) (U:=U) μ L) := by
  have he : lowerBase (X:=X) (U:=U) μ L=fun q => (1/2)*⟪lowerBaseHessian μ L q,q⟫ :=
    funext (lowerBase_eq_quadratic μ L)
  rw [he]
  exact contDiff_const.mul ((lowerBaseHessian (X:=X) (U:=U) μ L).contDiff.inner ℝ contDiff_id)

theorem lowerBase_hasGradientAt (μ L : ℝ) (q : FullMeanSpace (X:=X) (U:=U)) :
    HasGradientAt (lowerBase μ L) (lowerBaseHessian μ L q) q := by
  have he : lowerBase (X:=X) (U:=U) μ L=fun q => (1/2)*⟪lowerBaseHessian μ L q,q⟫ :=
    funext (lowerBase_eq_quadratic μ L)
  rw [he]
  have hd := (((lowerBaseHessian μ L).hasFDerivAt (x:=q)).inner ℝ (hasFDerivAt_id q)).const_mul (1/2:ℝ)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hd using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.coe_smul',Pi.smul_apply,
    smul_eq_mul,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,InnerProductSpace.toDual_apply,fderivInnerCLM_apply,ContinuousLinearMap.prod_apply,id_eq]
  rw [lowerBaseHessian_symmetric μ L v q,real_inner_comm v (lowerBaseHessian μ L q)]
  ring

theorem lowerBase_jets (μ L : ℝ) (hμ : 0≤μ) (hμL : μ≤L) (q : FullMeanSpace (X:=X) (U:=U)) :
    ‖iteratedFDeriv ℝ 2 (lowerBase μ L) q‖≤2*L ∧
    ‖iteratedFDeriv ℝ 3 (lowerBase μ L) q‖=0 := by
  have hL : 0≤L := hμ.trans hμL
  have hgrad : gradient (lowerBase (X:=X) (U:=U) μ L)=lowerBaseHessian μ L :=
    funext (fun q => (lowerBase_hasGradientAt μ L q).gradient)
  have hnorm : ‖lowerBaseHessian (X:=X) (U:=U) μ L‖≤2*L := by
    unfold lowerBaseHessian
    apply (norm_sub_le (μ • lowerProjection (X:=X) (U:=U)) (L • lowerSwap (X:=X) (U:=U))).trans
    have hm := ContinuousLinearMap.opNorm_smul_le μ (lowerProjection (X:=X) (U:=U))
    have hl := ContinuousLinearMap.opNorm_smul_le L (lowerSwap (X:=X) (U:=U))
    rw [Real.norm_eq_abs,abs_of_nonneg hμ] at hm
    rw [Real.norm_eq_abs,abs_of_nonneg hL] at hl
    have hmp := mul_le_mul_of_nonneg_left (lowerProjection_norm (X:=X) (U:=U)) hμ
    have hlp := mul_le_mul_of_nonneg_left (lowerSwap_norm (X:=X) (U:=U)) hL
    nlinarith only [hm,hl,hmp,hlp,hμL]
  constructor
  · rw [← GradientJetBounds.hessian_norm_eq (lowerBase_contDiff μ L),hgrad,
      (lowerBaseHessian (X:=X) (U:=U) μ L).fderiv]
    exact hnorm
  · rw [← GradientJetBounds.third_norm_eq (lowerBase_contDiff μ L),hgrad]
    have he : fderiv ℝ (lowerBaseHessian (X:=X) (U:=U) μ L)=fun _ => lowerBaseHessian μ L :=
      funext (fun y => (lowerBaseHessian (X:=X) (U:=U) μ L).fderiv)
    rw [he,fderiv_const]
    simp only [Pi.zero_apply]
    change ‖(0 : FullMeanSpace (X:=X) (U:=U) →L[ℝ]
      (FullMeanSpace (X:=X) (U:=U) →L[ℝ] FullMeanSpace (X:=X) (U:=U)))‖=0
    exact ContinuousLinearMap.opNorm_zero

end Bilevel.PolishedLiteral

