import Bilevel.SmallGapMean
import Bilevel.JointDerivative

/-! Full joint second derivatives of the actual three-dimensional small-gap
lift. The x-x block is zero and both mixed blocks are constant; hence variation
of the entire joint Hessian is exactly controlled by the proved y-y block. -/

noncomputable section
open scoped RealInnerProductSpace
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000

namespace Bilevel.SmallGapInstance.Parameters

open SmallGapLiftSupport
abbrev JointSpace := ℝ × LowerSpace

variable (P : Parameters)

def jointYDerivative (ω : ℝ) (z : JointSpace) : JointSpace →L[ℝ] LowerSpace :=
  (P.lowerYY ω z.2).comp (ContinuousLinearMap.snd ℝ ℝ LowerSpace) +
    ((-P.L) • ContinuousLinearMap.fst ℝ ℝ LowerSpace).smulRight e0

theorem lowerY_joint_hasFDerivAt (ω : ℝ) (z : JointSpace) :
    HasFDerivAt (fun v : JointSpace => P.lowerY ω v.1 v.2) (P.jointYDerivative ω z) z := by
  have hy := (P.lowerY_hasFDerivAt ω 0 z.2).comp z
    (ContinuousLinearMap.snd ℝ ℝ LowerSpace).hasFDerivAt
  have hx := ((ContinuousLinearMap.fst ℝ ℝ LowerSpace).hasFDerivAt (x := z)).const_mul (-P.L)
  have h := hy.add (hx.smul_const e0)
  convert h using 1
  funext v
  have he := P.lowerY_difference_x ω v.1 0 v.2
  simp only [sub_zero] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

def jointDerivative (ω : ℝ) (z : JointSpace) : JointSpace →L[ℝ] ℝ :=
  P.lowerX ω z.1 z.2 • ContinuousLinearMap.fst ℝ ℝ LowerSpace +
    (InnerProductSpace.toDual ℝ LowerSpace (P.lowerY ω z.1 z.2)).comp
      (ContinuousLinearMap.snd ℝ ℝ LowerSpace)

theorem lower_joint_hasFDerivAt (ω : ℝ) (hω : |ω| ≤ 1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) (z : JointSpace) :
    HasFDerivAt (fun v : JointSpace => P.lower ω v.1 v.2) (P.jointDerivative ω z) z := by
  have h := (P.primitive ω hω hscale).has_joint_g z.1 z.2
  change HasFDerivAt (fun v : JointSpace => P.lower ω v.1 v.2)
    ((InnerProductSpace.toDual ℝ ℝ (P.lowerX ω z.1 z.2)).comp (ContinuousLinearMap.fst ℝ ℝ LowerSpace) +
      (InnerProductSpace.toDual ℝ LowerSpace (P.lowerY ω z.1 z.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ LowerSpace)) z at h
  convert h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [jointDerivative, InnerProductSpace.toDual_apply, real_inner_comm, mul_comm]

def jointHessian (ω : ℝ) (z : JointSpace) : JointSpace →L[ℝ] JointSpace →L[ℝ] ℝ :=
  (P.lowerXY.comp (ContinuousLinearMap.snd ℝ ℝ LowerSpace)).smulRight
      (ContinuousLinearMap.fst ℝ ℝ LowerSpace) +
    ((ContinuousLinearMap.compL ℝ JointSpace LowerSpace ℝ).flip
      (ContinuousLinearMap.snd ℝ ℝ LowerSpace)).comp
        ((InnerProductSpace.toDual ℝ LowerSpace).toContinuousLinearMap.comp (P.jointYDerivative ω z))

theorem jointDerivative_hasFDerivAt (ω : ℝ) (z : JointSpace) :
    HasFDerivAt (P.jointDerivative ω) (P.jointHessian ω z) z := by
  have hx : HasFDerivAt (fun v : JointSpace => P.lowerX ω v.1 v.2)
      (P.lowerXY.comp (ContinuousLinearMap.snd ℝ ℝ LowerSpace)) z :=
    (P.lowerX_hasFDerivAt ω 0 z.2).comp z (ContinuousLinearMap.snd ℝ ℝ LowerSpace).hasFDerivAt
  have hy := (InnerProductSpace.toDual ℝ LowerSpace).toContinuousLinearMap.hasFDerivAt.comp z
    (P.lowerY_joint_hasFDerivAt ω z)
  have h := (hx.smul_const (ContinuousLinearMap.fst ℝ ℝ LowerSpace)).add
    (hy.clm_comp (hasFDerivAt_const (ContinuousLinearMap.snd ℝ ℝ LowerSpace) z))
  simpa only [ContinuousLinearMap.comp_zero, zero_add] using h

theorem jointHessian_difference_apply (ω : ℝ) (z z' v w : JointSpace) :
    (P.jointHessian ω z - P.jointHessian ω z') v w =
      ⟪(P.lowerYY ω z.2 - P.lowerYY ω z'.2) v.2, w.2⟫ := by
  simp [jointHessian, jointYDerivative, InnerProductSpace.toDual_apply, inner_sub_left,
    inner_add_left]

theorem jointHessian_difference_norm (ω : ℝ) (z z' : JointSpace) :
    ‖P.jointHessian ω z - P.jointHessian ω z'‖ ≤ ‖P.lowerYY ω z.2 - P.lowerYY ω z'.2‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro w
  rw [P.jointHessian_difference_apply]
  calc
    ‖⟪(P.lowerYY ω z.2 - P.lowerYY ω z'.2) v.2, w.2⟫‖ ≤
        ‖(P.lowerYY ω z.2 - P.lowerYY ω z'.2) v.2‖ * ‖w.2‖ := norm_inner_le_norm _ _
    _ ≤ (‖P.lowerYY ω z.2 - P.lowerYY ω z'.2‖ * ‖v.2‖) * ‖w.2‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (‖P.lowerYY ω z.2 - P.lowerYY ω z'.2‖ * ‖v‖) * ‖w‖ := by
      gcongr
      · exact norm_snd_le v
      · exact norm_snd_le w

theorem joint_second_derivative (ω : ℝ) (hω : |ω| ≤ 1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) (z : JointSpace) :
    fderiv ℝ (fderiv ℝ (fun v : JointSpace => P.lower ω v.1 v.2)) z = P.jointHessian ω z := by
  have he : fderiv ℝ (fun v : JointSpace => P.lower ω v.1 v.2) = P.jointDerivative ω := by
    funext v
    exact (P.lower_joint_hasFDerivAt ω hω hscale v).fderiv
  rw [he]
  exact (P.jointDerivative_hasFDerivAt ω z).fderiv

/-- The source's full joint-Hessian variation statement, for the actual second
Fréchet derivative rather than only the lower-lower block. -/
theorem full_joint_hessian_variation (ω : ℝ) (hω : |ω| ≤ 1)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) (z z' : JointSpace) :
    ‖fderiv ℝ (fderiv ℝ (fun v : JointSpace => P.lower ω v.1 v.2)) z -
      fderiv ℝ (fderiv ℝ (fun v : JointSpace => P.lower ω v.1 v.2)) z'‖ ≤
        P.rawRho * Model.jointDistance z.1 z'.1 z.2 z'.2 := by
  rw [P.joint_second_derivative ω hω hscale z, P.joint_second_derivative ω hω hscale z']
  exact (P.jointHessian_difference_norm ω z z').trans
    (P.hessian_variation_joint ω hω hscale z.1 z'.1 z.2 z'.2)

end Bilevel.SmallGapInstance.Parameters
