import Bilevel.CompensatedMeanPrimitive
import Bilevel.JointDerivative
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Full joint derivatives of the actual compensated mean lift. All varying
second derivatives are in the lower-lower block; the two mixed blocks are
constant. Thus the source's full Hessian variation follows from the proved
third derivative budget for the actual perturbation. -/

noncomputable section
namespace Bilevel.CompensatedMean
open scoped RealInnerProductSpace
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 100000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
abbrev JointSpace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := E × LowerSpace E

local instance : NormedAddCommGroup (JointSpace E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (JointSpace E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (JointSpace E →L[ℝ] JointSpace E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (JointSpace E →L[ℝ] JointSpace E →L[ℝ] ℝ) := inferInstance

theorem uProj_adjoint (x : E) : (uProj E).adjoint x = pack E x 0 0 := by
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left,inner_pack]
  simp only [zero_mul,add_zero]

namespace Data
variable (P : Data (E := E))

omit [CompleteSpace E] in
theorem lower_joint_contDiff : ContDiff ℝ 3 (fun v : JointSpace E => P.lower v.1 v.2) := by
  have h := (P.lower_contDiff 0).comp (contDiff_snd (E := E))
  have hx : ContDiff ℝ 3 (fun v : JointSpace E => v.1) := contDiff_fst
  have hu : ContDiff ℝ 3 (fun v : JointSpace E => uProj E v.2) :=
    (uProj E).contDiff.comp contDiff_snd
  have hh := h.sub ((hx.inner ℝ hu).const_smul P.L)
  convert hh using 1
  funext v
  simp only [lower,inner_zero_left,mul_zero,sub_zero,Function.comp_apply,smul_eq_mul]
  ring

omit [CompleteSpace E] in
theorem upper_joint_contDiff : ContDiff ℝ 3 (fun v : JointSpace E => P.upper v.1 v.2) :=
  (P.upper_contDiff 0).comp contDiff_snd

def jointYDerivative (z : JointSpace E) : JointSpace E →L[ℝ] LowerSpace E :=
  (P.lowerYY z.2).comp (ContinuousLinearMap.snd ℝ E (LowerSpace E))-
    P.L • ((uProj E).adjoint.comp (ContinuousLinearMap.fst ℝ E (LowerSpace E)))

theorem lowerY_joint_hasFDerivAt (z : JointSpace E) :
    HasFDerivAt (fun v : JointSpace E => P.lowerY v.1 v.2) (P.jointYDerivative z) z := by
  have hy := (P.lowerY_hasFDerivAt 0 z.2).comp z
    (ContinuousLinearMap.snd ℝ E (LowerSpace E)).hasFDerivAt
  have hx := (((uProj E).adjoint.comp (ContinuousLinearMap.fst ℝ E (LowerSpace E))).hasFDerivAt
    (x := z)).const_smul P.L
  convert hy.sub hx using 1
  funext v
  simp only [Function.comp_apply]
  rw [P.lowerY_decomposition v.1 v.2,P.lowerY_decomposition 0 v.2]
  simp only [smul_zero,pack_zero,sub_zero,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst',uProj_adjoint]
  have he : pack E (P.L • v.1) 0 0 = P.L • pack E v.1 0 0 := by
    simpa only [mul_zero] using pack_smul P.L v.1 0 0
  rw [he]
  abel

def jointDerivative (z : JointSpace E) : JointSpace E →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ E (P.lowerX z.1 z.2)).comp
      (ContinuousLinearMap.fst ℝ E (LowerSpace E))+
    (InnerProductSpace.toDual ℝ (LowerSpace E) (P.lowerY z.1 z.2)).comp
      (ContinuousLinearMap.snd ℝ E (LowerSpace E))

theorem lower_joint_hasFDerivAt (z : JointSpace E) :
    HasFDerivAt (fun v : JointSpace E => P.lower v.1 v.2) (P.jointDerivative z) z := by
  have hy := (P.lower_hasGradientY 0 z.2).hasFDerivAt.comp z
    (ContinuousLinearMap.snd ℝ E (LowerSpace E)).hasFDerivAt
  have hx := ((ContinuousLinearMap.fst ℝ E (LowerSpace E)).hasFDerivAt (x := z)).inner ℝ
    (((uProj E).comp (ContinuousLinearMap.snd ℝ E (LowerSpace E))).hasFDerivAt (x := z))
  convert hy.sub (hx.const_mul P.L) using 1
  · funext v
    simp only [Function.comp_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd',lower,inner_zero_left,mul_zero,sub_zero]
    ring
  apply ContinuousLinearMap.ext
  intro v
  simp only [jointDerivative,lowerX,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',InnerProductSpace.toDual_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    fderivInnerCLM_apply,ContinuousLinearMap.prod_apply,real_inner_smul_left]
  rw [P.lowerY_decomposition z.1 z.2,P.lowerY_decomposition 0 z.2]
  simp only [smul_zero,pack_zero,sub_zero,inner_sub_left,inner_add_left,inner_pack,
    real_inner_smul_left,zero_mul,add_zero]
  rw [real_inner_comm v.1 (uProj E z.2)]
  ring

def jointHessian (z : JointSpace E) : JointSpace E →L[ℝ] JointSpace E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (JointSpace E) E ℝ).flip
      (ContinuousLinearMap.fst ℝ E (LowerSpace E))).comp
        ((InnerProductSpace.toDual ℝ E).toLinearIsometry.toContinuousLinearMap.comp
          (P.lowerXY.comp (ContinuousLinearMap.snd ℝ E (LowerSpace E))))+
    ((ContinuousLinearMap.compL ℝ (JointSpace E) (LowerSpace E) ℝ).flip
      (ContinuousLinearMap.snd ℝ E (LowerSpace E))).comp
        ((InnerProductSpace.toDual ℝ (LowerSpace E)).toLinearIsometry.toContinuousLinearMap.comp (P.jointYDerivative z))

theorem jointDerivative_hasFDerivAt (z : JointSpace E) :
    HasFDerivAt P.jointDerivative (P.jointHessian z) z := by
  have hx := (InnerProductSpace.toDual ℝ E).toLinearIsometry.toContinuousLinearMap.hasFDerivAt.comp z
    ((P.lowerX_hasFDerivAt 0 z.2).comp z (ContinuousLinearMap.snd ℝ E (LowerSpace E)).hasFDerivAt)
  have hy := (InnerProductSpace.toDual ℝ (LowerSpace E)).toLinearIsometry.toContinuousLinearMap.hasFDerivAt.comp z
    (P.lowerY_joint_hasFDerivAt z)
  exact ((((ContinuousLinearMap.compL ℝ (JointSpace E) E ℝ).flip
    (ContinuousLinearMap.fst ℝ E (LowerSpace E))).hasFDerivAt.comp z hx).add
    (((ContinuousLinearMap.compL ℝ (JointSpace E) (LowerSpace E) ℝ).flip
      (ContinuousLinearMap.snd ℝ E (LowerSpace E))).hasFDerivAt.comp z hy))

theorem jointHessian_difference_apply (z z' v w : JointSpace E) :
    (P.jointHessian z-P.jointHessian z') v w =
      ⟪(P.lowerYY z.2-P.lowerYY z'.2) v.2,w.2⟫ := by
  simp [jointHessian,jointYDerivative,InnerProductSpace.toDual_apply,inner_sub_left]

theorem jointHessian_difference_norm (z z' : JointSpace E) :
    ‖P.jointHessian z-P.jointHessian z'‖ ≤ ‖P.lowerYY z.2-P.lowerYY z'.2‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (P.jointHessian z-P.jointHessian z')
    (norm_nonneg (P.lowerYY z.2-P.lowerYY z'.2))
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro w
  rw [P.jointHessian_difference_apply]
  calc
    _ ≤ ‖(P.lowerYY z.2-P.lowerYY z'.2) v.2‖*‖w.2‖ := norm_inner_le_norm _ _
    _ ≤ (‖P.lowerYY z.2-P.lowerYY z'.2‖*‖v.2‖)*‖w.2‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (‖P.lowerYY z.2-P.lowerYY z'.2‖*‖v‖)*‖w‖ := by
      gcongr
      · exact norm_snd_le v
      · exact norm_snd_le w

theorem joint_second_derivative (z : JointSpace E) :
    fderiv ℝ (fderiv ℝ (fun v : JointSpace E => P.lower v.1 v.2)) z = P.jointHessian z := by
  have he : fderiv ℝ (fun v : JointSpace E => P.lower v.1 v.2) = P.jointDerivative :=
    funext (fun v => (P.lower_joint_hasFDerivAt v).fderiv)
  rw [he]
  exact (P.jointDerivative_hasFDerivAt z).fderiv

theorem full_joint_hessian_variation (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hthird : ∀ y,‖iteratedFDeriv ℝ 3 P.perturbation y‖ ≤ ρ) (z z' : JointSpace E) :
    ‖fderiv ℝ (fderiv ℝ (fun v : JointSpace E => P.lower v.1 v.2)) z-
      fderiv ℝ (fderiv ℝ (fun v : JointSpace E => P.lower v.1 v.2)) z'‖ ≤
        ρ*Model.jointDistance z.1 z'.1 z.2 z'.2 := by
  rw [P.joint_second_derivative z,P.joint_second_derivative z']
  apply (P.jointHessian_difference_norm z z').trans
  apply (P.lowerYY_variation ρ hthird z.2 z'.2).trans
  apply mul_le_mul_of_nonneg_left _ hρ
  unfold Model.jointDistance
  rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
  nlinarith [sq_nonneg ‖z.1-z'.1‖]

theorem upper_joint_hasFDerivAt (z : JointSpace E) :
    HasFDerivAt (fun v : JointSpace E => P.upper v.1 v.2)
      ((InnerProductSpace.toDual ℝ (LowerSpace E) (P.upperY z.1 z.2)).comp
        (ContinuousLinearMap.snd ℝ E (LowerSpace E))) z :=
  (P.upper_hasGradientY z.1 z.2).hasFDerivAt.comp z
    (ContinuousLinearMap.snd ℝ E (LowerSpace E)).hasFDerivAt

theorem full_upper_derivative_bound (Cf : ℝ) (hCf : 0 ≤ Cf)
    (hbound : ∀ x y,‖P.upperY x y‖ ≤ Cf) (z : JointSpace E) :
    ‖fderiv ℝ (fun v : JointSpace E => P.upper v.1 v.2) z‖ ≤ Cf := by
  rw [(P.upper_joint_hasFDerivAt z).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ hCf
  intro v
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',InnerProductSpace.toDual_apply]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul (hbound z.1 z.2) (norm_snd_le v) (norm_nonneg _) hCf)

theorem full_upper_gradient_bound (Cf : ℝ)
    (hbound : ∀ x y,‖P.upperY x y‖ ≤ Cf) (x : E) (y : LowerSpace E) :
    Real.sqrt (‖P.upperX x y‖^2+‖P.upperY x y‖^2) ≤ Cf := by
  simpa only [upperX,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add,Real.sqrt_sq_eq_abs,
    abs_norm] using hbound x y

end Data
end Bilevel.CompensatedMean
