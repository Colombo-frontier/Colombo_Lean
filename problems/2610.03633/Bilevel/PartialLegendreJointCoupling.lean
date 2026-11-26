import Bilevel.PartialLegendreJointHessian
import Bilevel.PartialLegendreJointResponse
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Full joint regularity of the actual scaled partial conjugate with the
bilinear source coupling. All outer, coupling, and lower variables vary. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X Y W U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

def bilinearCouplingOperator (A B : W →L[ℝ] U) : W →L[ℝ] W :=
  A.adjoint.comp B+B.adjoint.comp A

theorem bilinearCouplingOperator_norm (A B : W →L[ℝ] U)
    (hA : ‖A‖≤1) (hB : ‖B‖≤1) : ‖bilinearCouplingOperator A B‖≤2 := by
  have ha : ‖A.adjoint.comp B‖≤1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map]
    nlinarith [norm_nonneg A,norm_nonneg B]
  have hb : ‖B.adjoint.comp A‖≤1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map]
    nlinarith [norm_nonneg A,norm_nonneg B]
  exact (norm_add_le _ _).trans (by linarith)

variable {δ : NNReal} {G : Joint X Y → Joint X Y}
  (hG : LipschitzWith δ G) (hδ : δ<1) (P : Joint X Y → ℝ)

def conjugateCoupling (T : W →L[ℝ] Joint X Y) (A B : W →L[ℝ] U)
    (m c : ℝ) (q : W) : ℝ :=
  m*jointConjugate hG hδ P (T q)-c*⟪A q,B q⟫

variable (hP : ∀ q,HasGradientAt P (G q) q)
include hP

theorem conjugateCoupling_hasGradientAt (T : W →L[ℝ] Joint X Y) (A B : W →L[ℝ] U)
    (m c : ℝ) (q : W) :
    HasGradientAt (conjugateCoupling hG hδ P T A B m c)
      (m • T.adjoint (jointGradient hG hδ (T q))-c • bilinearCouplingOperator A B q) q := by
  have hl := (jointConjugate_hasGradientAt hG hδ P hP (T q)).hasFDerivAt.comp q T.hasFDerivAt
  have hb := A.hasFDerivAt.inner ℝ B.hasFDerivAt (x := q)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert (hl.const_mul m).sub (hb.const_mul c) using 1
  ext v
  simp only [InnerProductSpace.toDual_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.prod_apply,
    bilinearCouplingOperator,fderivInnerCLM_apply,inner_sub_left,inner_add_left,
    real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left,smul_eq_mul]
  rw [real_inner_comm (B q) (A v)]
  ring

theorem conjugateCoupling_gradient (T : W →L[ℝ] Joint X Y) (A B : W →L[ℝ] U)
    (m c : ℝ) (q : W) :
    gradient (conjugateCoupling hG hδ P T A B m c) q=
      m • T.adjoint (jointGradient hG hδ (T q))-c • bilinearCouplingOperator A B q :=
  (conjugateCoupling_hasGradientAt hG hδ P hP T A B m c q).gradient

omit hP in
def conjugateCouplingHessian (T : W →L[ℝ] Joint X Y) (A B : W →L[ℝ] U)
    (m c : ℝ) (K : Joint X Y → Joint X Y →L[ℝ] Joint X Y) (q : W) : W →L[ℝ] W :=
  m • T.adjoint.comp ((K (T q)).comp T)-c • bilinearCouplingOperator A B

theorem conjugateCoupling_gradient_hasFDerivAt
    (T : W →L[ℝ] Joint X Y) (A B : W →L[ℝ] U) (m c : ℝ)
    (K : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hK : ∀ z,HasFDerivAt (gradient (jointConjugate hG hδ P)) (K z) z) (q : W) :
    HasFDerivAt (gradient (conjugateCoupling hG hδ P T A B m c))
      (conjugateCouplingHessian T A B m c K q) q := by
  have he : gradient (conjugateCoupling hG hδ P T A B m c)=
      (fun v => m • T.adjoint (gradient (jointConjugate hG hδ P) (T v))-
        c • bilinearCouplingOperator A B v) := by
    funext v
    rw [conjugateCoupling_gradient hG hδ P hP,jointConjugate_gradient hG hδ P hP]
  rw [he]
  exact ((T.adjoint.hasFDerivAt.comp q ((hK (T q)).comp q T.hasFDerivAt)).const_smul m).sub
    ((bilinearCouplingOperator A B).hasFDerivAt.const_smul c)

omit hP in
theorem conjugateCouplingHessian_norm (T : W →L[ℝ] Joint X Y) (A B : W →L[ℝ] U)
    (hT : ‖T‖≤1) (hA : ‖A‖≤1) (hB : ‖B‖≤1) {m : ℝ} (hm : 0≤m) (c : ℝ)
    (K : Joint X Y → Joint X Y →L[ℝ] Joint X Y) {C : ℝ}
    (hK : ∀ z,‖K z‖≤C) (q : W) :
    ‖conjugateCouplingHessian T A B m c K q‖≤m*C+2*|c| := by
  have hC : 0≤C := (norm_nonneg (K (T q))).trans (hK _)
  have ht : ‖T.adjoint.comp ((K (T q)).comp T)‖≤C := by
    calc
      _ ≤ ‖T.adjoint‖*(‖K (T q)‖*‖T‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1*(C*1) := by rw [ContinuousLinearMap.adjoint.norm_map]; gcongr; exact hK _
      _ = C := by ring
  calc
    _ ≤ ‖m • T.adjoint.comp ((K (T q)).comp T)‖+‖c • bilinearCouplingOperator A B‖ := norm_sub_le _ _
    _ = m*‖T.adjoint.comp ((K (T q)).comp T)‖+|c| * ‖bilinearCouplingOperator A B‖ := by
      rw [norm_smul m (T.adjoint.comp ((K (T q)).comp T)),
        norm_smul c (bilinearCouplingOperator A B),Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hm]
    _ ≤ m*C+|c| * 2 := add_le_add (mul_le_mul_of_nonneg_left ht hm)
      (mul_le_mul_of_nonneg_left (bilinearCouplingOperator_norm A B hA hB) (abs_nonneg c))
    _ = _ := by ring

omit hP in
theorem conjugateCouplingHessian_variation (T : W →L[ℝ] Joint X Y) (A B : W →L[ℝ] U)
    (hT : ‖T‖≤1) {m : ℝ} (hm : 0≤m) (c : ℝ)
    (K : Joint X Y → Joint X Y →L[ℝ] Joint X Y) {C : ℝ} (hC : 0≤C)
    (hK : ∀ z w,‖K z-K w‖≤C*‖z-w‖) (q r : W) :
    ‖conjugateCouplingHessian T A B m c K q-conjugateCouplingHessian T A B m c K r‖≤
      m*C*‖q-r‖ := by
  have he : conjugateCouplingHessian T A B m c K q-conjugateCouplingHessian T A B m c K r=
      m • T.adjoint.comp (((K (T q))-(K (T r))).comp T) := by
    ext v
    simp only [conjugateCouplingHessian,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,map_sub,smul_sub]
    abel
  rw [he,norm_smul m (T.adjoint.comp ((K (T q)-K (T r)).comp T)),Real.norm_eq_abs,abs_of_nonneg hm]
  have ht : ‖T q-T r‖≤‖q-r‖ := by
    rw [← map_sub]
    exact (T.le_opNorm _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hT (norm_nonneg (q-r)))
  calc
    _ ≤ m*(‖T.adjoint‖*(‖K (T q)-K (T r)‖*‖T‖)) :=
      mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))) hm
    _ ≤ m*(1*((C*‖q-r‖)*1)) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      gcongr
      exact (hK _ _).trans (mul_le_mul_of_nonneg_left ht hC)
    _ = _ := by ring

omit hP [CompleteSpace X] [CompleteSpace W] [CompleteSpace U] in
theorem conjugateCoupling_contDiff_two (T : W →L[ℝ] Joint X Y) (A B : W →L[ℝ] U)
    (m c : ℝ) (hL : ContDiff ℝ 2 (jointConjugate hG hδ P)) :
    ContDiff ℝ 2 (conjugateCoupling hG hδ P T A B m c) :=
  (contDiff_const.mul (hL.comp T.contDiff)).sub (contDiff_const.mul (A.contDiff.inner ℝ B.contDiff))

end Bilevel.PartialLegendre
