import NCConcave16991.ConeSmoothStage
import NCConcave16991.ConeProblemRecovery

/-! # Actual cone individual smoothness and arbitrary-output certificate

The universal constant depends only on the single fixed density. All
component Hessians, gradients and constrained primal values are actual
derivatives and maxima of the literal construction.
-/

noncomputable section

namespace NCConcave16991.ConeSmooth

open ConeValue ConeProblem Set Metric
open scoped InnerProductSpace ContDiff

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 4
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n M : ℕ}

theorem jointCylinder_convex (R : ℝ) : Convex ℝ {x : JointBlocks E M | ‖x.snd‖ ≤ R} := by
  have hh := (convex_closedBall (0 : Blocks E M) R).linear_preimage
    (WithLp.sndL 2 ℝ (PrimalBlocks E M) (Blocks E M)).toLinearMap
  convert hh using 1
  ext x
  simp only [mem_setOf_eq, mem_preimage, mem_closedBall, dist_zero_right, ContinuousLinearMap.coe_coe]
  rfl

theorem jointComponent_fderiv_sub_bound (hn : 0 < n) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 1 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R) (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j))
    (i : Fin n) (x y : JointBlocks E M) (hx : ‖x.snd‖ ≤ R) (hy : ‖y.snd‖ ≤ R) :
    ‖fderiv ℝ (jointComponent R q w i) x - fderiv ℝ (jointComponent R q w i) y‖ ≤
      individualConstant * ‖x - y‖ := by
  have hs := component_contDiff (by linarith : q ≠ 0) R w i
  have hd : Differentiable ℝ (fderiv ℝ (jointComponent R q w i)) :=
    (hs.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := {z : JointBlocks E M | ‖z.snd‖ ≤ R}) (𝕜 := ℝ)
    (f := fderiv ℝ (jointComponent R q w i)) (fun z hz ↦ hd z)
    (fun z hz ↦ jointComponent_hessian_norm_le hn hR hq hrel hq2 w hw i z hz)
    (jointCylinder_convex R) hy hx

variable [FiniteDimensional ℝ E]

/-- The actual Euclidean `Problem` belongs to IS with a universal constant.
No desired smoothness statement is a premise of this theorem. -/
theorem problem_individualSmooth (hn : 0 < n) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 16 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R) (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j)) :
    (ConeProblem.problem hn individualConstant individualConstant_pos R (by linarith) q (by linarith) w hw).individualSmooth := by
  intro i x hx y hy
  change ‖gradient (ConeProblem.component R q w i) x - gradient (ConeProblem.component R q w i) y‖ ≤
    individualConstant * ‖x - y‖
  have he : ‖gradient (ConeProblem.component R q w i) x - gradient (ConeProblem.component R q w i) y‖ =
      ‖fderiv ℝ (ConeProblem.component R q w i) x - fderiv ℝ (ConeProblem.component R q w i) y‖ := by
    rw [← (InnerProductSpace.toDual ℝ (JointSpace (primalDimension E M) (dualDimension E M))).norm_map,
      map_sub, toDual_gradient, toDual_gradient]
  rw [he]
  let e := (jointCoordinates E M).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hd (z : JointSpace (primalDimension E M) (dualDimension E M)) :
      fderiv ℝ (ConeProblem.component R q w i) z =
        (fderiv ℝ (jointComponent R q w i) ((jointCoordinates E M).symm z)).comp e := by
    exact (((component_contDiff (by linarith : q ≠ 0) R w i).differentiable (by simp)
      ((jointCoordinates E M).symm z)).hasFDerivAt.comp z
        (jointCoordinates E M).symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
  rw [hd, hd, ← ContinuousLinearMap.sub_comp]
  have heNorm : ‖e‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    intro z
    exact (jointCoordinates E M).symm.norm_map z |>.le.trans_eq (one_mul _).symm
  have hxn : ‖x.snd‖ ≤ R := by
    simpa only [productDomain, dualDomain, mem_setOf_eq, mem_closedBall, dist_zero_right] using hx
  have hyn : ‖y.snd‖ ≤ R := by
    simpa only [productDomain, dualDomain, mem_setOf_eq, mem_closedBall, dist_zero_right] using hy
  have hxd : ‖((jointCoordinates E M).symm x).snd‖ ≤ R := by
    change ‖(dualCoordinates E M).symm x.snd‖ ≤ R
    simpa only [LinearIsometryEquiv.norm_map] using hxn
  have hyd : ‖((jointCoordinates E M).symm y).snd‖ ≤ R := by
    change ‖(dualCoordinates E M).symm y.snd‖ ≤ R
    simpa only [LinearIsometryEquiv.norm_map] using hyn
  have hb := jointComponent_fderiv_sub_bound hn hR (by linarith) hrel hq2 w hw i
    ((jointCoordinates E M).symm x) ((jointCoordinates E M).symm y) hxd hyd
  rw [← map_sub, LinearIsometryEquiv.norm_map] at hb
  exact ((fderiv ℝ (jointComponent R q w i) ((jointCoordinates E M).symm x) -
      fderiv ℝ (jointComponent R q w i) ((jointCoordinates E M).symm y)).opNorm_comp_le e).trans
    ((mul_le_mul hb heNorm (norm_nonneg _) (mul_nonneg individualConstant_pos.le (norm_nonneg _))).trans_eq (mul_one _))

theorem problem_averagedSmooth (hn : 0 < n) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 16 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R) (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j)) :
    (ConeProblem.problem hn individualConstant individualConstant_pos R (by linarith) q (by linarith) w hw).averagedSmooth :=
  Problem.individual_implies_averaged _ (problem_individualSmooth hn hR hq hrel hq2 w hw)

/-- The original Moreau stationarity of any arbitrary output forces all its
decoded source blocks to be close to their actual hidden means. This version
has no IS/AS premise: admissibility is proved above for the literal instance. -/
theorem stationary_output_source_certificate (hn : 0 < n) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 16 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R) (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j))
    (c : PrimalSpace (primalDimension E M))
    (hc : StationaryOutput
      (ConeProblem.problem hn individualConstant individualConstant_pos R (by linarith) q (by linarith) w hw) c) :
    ∀ j, ‖((primalCoordinates E M).symm c).fst j - sourceMean w j‖ ≤
      (1 / 1000) / (2 * individualConstant) :=
  stationary_output_source_distance hn individualConstant individualConstant_pos R (by linarith) q hq w hw
    (problem_averagedSmooth hn hR hq hrel hq2 w hw) c hc

theorem cap_score_of_near_unit (z v : E) (hv : ‖v‖ = 1) (hnear : ‖z - v‖ ≤ 1 / 4) :
    3 / 4 ≤ ⟪ConeRadial.zeta z, v⟫_ℝ := by
  have hz : ‖z‖ ≤ 2 := by
    have hh := norm_add_le (z - v) v
    rw [sub_add_cancel, hv] at hh
    linarith
  rw [ConeRadial.zeta_identity hz]
  have hi := abs_real_inner_le_norm (z - v) v
  rw [hv, mul_one] at hi
  have hn := (abs_le.mp hi).1
  rw [inner_sub_left, real_inner_self_eq_norm_sq, hv] at hn
  nlinarith

/-- The normalized capped output probe has a fixed positive correlation
with every source. This is an actual arbitrary-output certificate suitable
for the Haar source-recovery charge. -/
theorem stationary_output_source_probe (hn : 0 < n) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 16 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R) (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j))
    (c : PrimalSpace (primalDimension E M))
    (hc : StationaryOutput
      (ConeProblem.problem hn individualConstant individualConstant_pos R (by linarith) q (by linarith) w hw) c) :
    ∀ j, ‖(1 / 3 : ℝ) • ConeRadial.zeta (((primalCoordinates E M).symm c).fst j)‖ ≤ 1 ∧
      1 / 4 ≤ ⟪(1 / 3 : ℝ) • ConeRadial.zeta (((primalCoordinates E M).symm c).fst j), sourceMean w j⟫_ℝ := by
  intro j
  have hnear := stationary_output_source_certificate hn hR hq hrel hq2 w hw c hc j
  have hC : (100000 : ℝ) ≤ individualConstant := by
    have hh := densitySlopeBound_nonneg
    unfold individualConstant
    nlinarith
  have hδ : (1 / 1000 : ℝ) / (2 * individualConstant) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) individualConstant_pos)).mpr
    linarith
  have hscore := cap_score_of_near_unit (((primalCoordinates E M).symm c).fst j) (sourceMean w j)
    (sourceMean_unit hn w hw j) (hnear.trans hδ)
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
    nlinarith [ConeRadial.zeta_norm_bound (((primalCoordinates E M).symm c).fst j)]
  · rw [real_inner_smul_left]
    linarith

end NCConcave16991.ConeSmooth
