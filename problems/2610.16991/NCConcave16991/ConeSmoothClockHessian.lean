import NCConcave16991.ConeSmoothClock
import NCConcave16991.GlobalHardDerivativeRules

/-! # Dimension-free Hessian bound for a complete guarded clock -/

noncomputable section

namespace NCConcave16991.ConeSmooth

open ConePrimitives ConeRadial ConeClockGap ConeRecovery Set
open scoped InnerProductSpace ContDiff

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def quadratic (q : ℝ) (u : E) : ℝ := ‖u‖ ^ 2 / (2 * q)

theorem quadratic_fderiv {q : ℝ} (hq : 0 < q) (u : E) :
    fderiv ℝ (quadratic q : E → ℝ) u = q⁻¹ • innerSL ℝ u := by
  have hh := (hasStrictFDerivAt_norm_sq u).hasFDerivAt.mul_const ((2 * q)⁻¹)
  change HasFDerivAt (quadratic q : E → ℝ) _ u at hh
  rw [hh.fderiv]
  ext h
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  field_simp
  simp [smul_eq_mul]

theorem quadratic_fderiv_sub_bound {q : ℝ} (hq : 1 ≤ q) (x y : E) :
    ‖fderiv ℝ (quadratic q : E → ℝ) x - fderiv ℝ (quadratic q : E → ℝ) y‖ ≤ ‖x - y‖ := by
  have hq0 : 0 < q := by linarith
  rw [quadratic_fderiv hq0, quadratic_fderiv hq0, ← smul_sub, ← map_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq0), innerSL_apply_norm]
  have hi : q⁻¹ ≤ 1 := by exact (inv_le_one₀ hq0).mpr hq
  exact (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans_eq (one_mul _)

def localClock (q : ℝ) (v : E) (p : Pair E) : ℝ := clock q v p.fst p.snd

theorem localClock_fderiv_sub_bound {q : ℝ} (hq : 1 ≤ q) (v : E) (hv : ‖v‖ = 1)
    (x y : Pair E) :
    ‖fderiv ℝ (localClock q v) x - fderiv ℝ (localClock q v) y‖ ≤
      (24743 + 640 * densitySlopeBound) * ‖x - y‖ := by
  let f : Pair E → ℝ := fun p ↦ rootNorm 1 (pairU p) - 1
  let g : Pair E → ℝ := fun p ↦ quadratic q (pairU p)
  let h : Pair E → ℝ := fun p ↦ (-10) * theta (clockArgument v p.fst p.snd)
  have hf : ContDiff ℝ ∞ f := ((rootNorm_contDiff (by norm_num : (0 : ℝ) < 1)).comp
    (pairU (E := E)).contDiff).sub contDiff_const
  have hg : ContDiff ℝ ∞ g := ((contDiff_norm_sq ℝ).comp (pairU (E := E)).contDiff).div_const (2 * q)
  have ht := theta_argument_derivativeBound v hv
  have hh : ContDiff ℝ ∞ h := contDiff_const.mul ht.smooth
  have hfd (p : Pair E) : fderiv ℝ f p = fderiv ℝ (fun p : Pair E ↦ rootNorm 1 (pairU p)) p :=
    (((rootNorm_contDiff (by norm_num : (0 : ℝ) < 1)).comp (pairU (E := E)).contDiff).differentiable
      (by simp) p).hasFDerivAt.sub_const 1 |>.fderiv
  have hfc (a b : Pair E) : ‖fderiv ℝ f a - fderiv ℝ f b‖ ≤ 2 * ‖a - b‖ := by
    rw [hfd, hfd]
    have hb := (rootNorm_derivativeBound (E := E) (by norm_num : (0 : ℝ) < 1)).comp_contraction
      (pairU (E := E)) pairU_norm
    simpa only [Real.sqrt_one, div_one] using hb.second a b
  have hquadratic : ContDiff ℝ ∞ (quadratic q : E → ℝ) := (contDiff_norm_sq ℝ).div_const (2 * q)
  have hgc (a b : Pair E) : ‖fderiv ℝ g a - fderiv ℝ g b‖ ≤ 1 * ‖a - b‖ :=
    GlobalHard.fderiv_sub_bound_comp_contraction (quadratic q)
      (hquadratic.differentiable (by simp))
      1 (by norm_num) (fun a b ↦ by simpa only [one_mul] using quadratic_fderiv_sub_bound hq a b)
      (pairU (E := E)) pairU_norm a b
  have hhc (a b : Pair E) : ‖fderiv ℝ h a - fderiv ℝ h b‖ ≤
      (10 * (64 * densitySlopeBound + 2474)) * ‖a - b‖ := by
    simpa only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 10)] using (ht.const_mul (-10)).second a b
  have hfg := GlobalHard.fderiv_sub_bound_add f g (hf.differentiable (by simp)) (hg.differentiable (by simp))
    2 1 hfc hgc
  have hsum := GlobalHard.fderiv_sub_bound_add (fun p ↦ f p + g p) h
    ((hf.add hg).differentiable (by simp)) (hh.differentiable (by simp))
    (2 + 1) (10 * (64 * densitySlopeBound + 2474)) hfg hhc x y
  have he : localClock q v = fun p ↦ f p + g p + h p := by
    funext p
    dsimp [localClock, clock, f, g, h, quadratic, rootNorm, pairU, clockArgument]
    simp only [WithLp.sndL_apply]
    ring
  rw [he]
  convert hsum using 1 <;> ring

theorem guard_fderiv_sub_bound (x y : E) :
    ‖fderiv ℝ (ConeRadial.guard 3000 : E → ℝ) x -
      fderiv ℝ (ConeRadial.guard 3000 : E → ℝ) y‖ ≤ 12000 * ‖x - y‖ := by
  have hD : Differentiable ℝ (fderiv ℝ (ConeRadial.guard 3000 : E → ℝ)) :=
    ((guard_contDiff 3000).fderiv_right (m := 1) (by simp)).differentiable one_ne_zero
  have hg : Differentiable ℝ (gradient (ConeRadial.guard 3000 : E → ℝ)) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.differentiable.comp hD
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (𝕜 := ℝ)
    (f := gradient (ConeRadial.guard 3000 : E → ℝ)) (fun z _ ↦ hg z)
    (fun z _ ↦ by simpa only [show (4 : ℝ) * 3000 = 12000 by norm_num] using
      guard_hessian_norm_le (by norm_num : (0 : ℝ) ≤ 3000) z)
    convex_univ (mem_univ y) (mem_univ x)
  have he : ‖gradient (ConeRadial.guard 3000 : E → ℝ) x -
      gradient (ConeRadial.guard 3000 : E → ℝ) y‖ =
      ‖fderiv ℝ (ConeRadial.guard 3000 : E → ℝ) x - fderiv ℝ (ConeRadial.guard 3000 : E → ℝ) y‖ := by
    rw [← (InnerProductSpace.toDual ℝ E).norm_map, map_sub, toDual_gradient, toDual_gradient]
  rw [he] at hh
  exact hh

def localGuardedClock (q : ℝ) (v : E) (p : Pair E) : ℝ := localClock q v p + ConeRadial.guard 3000 p.fst

theorem localGuardedClock_fderiv_sub_bound {q : ℝ} (hq : 1 ≤ q) (v : E) (hv : ‖v‖ = 1)
    (x y : Pair E) :
    ‖fderiv ℝ (localGuardedClock q v) x - fderiv ℝ (localGuardedClock q v) y‖ ≤
      (36743 + 640 * densitySlopeBound) * ‖x - y‖ := by
  have hc : ContDiff ℝ ∞ (localClock q v) := clock_contDiff v (pairZ (E := E)).contDiff (pairU (E := E)).contDiff
  have hg : ContDiff ℝ ∞ (fun p : Pair E ↦ ConeRadial.guard 3000 p.fst) :=
    (guard_contDiff 3000).comp (pairZ (E := E)).contDiff
  have hgc := GlobalHard.fderiv_sub_bound_comp_contraction (ConeRadial.guard 3000 : E → ℝ)
    ((guard_contDiff 3000).differentiable (by simp)) 12000 (by norm_num) guard_fderiv_sub_bound
    (pairZ (E := E)) pairZ_norm
  have hh := GlobalHard.fderiv_sub_bound_add (localClock q v) (fun p : Pair E ↦ ConeRadial.guard 3000 p.fst)
    (hc.differentiable (by simp)) (hg.differentiable (by simp))
    (24743 + 640 * densitySlopeBound) 12000 (localClock_fderiv_sub_bound hq v hv) hgc x y
  convert hh using 1
  all_goals try rfl
  all_goals ring

theorem localGuardedClock_hessian_norm_le {q : ℝ} (hq : 1 ≤ q) (v : E) (hv : ‖v‖ = 1)
    (x : Pair E) : ‖fderiv ℝ (fderiv ℝ (localGuardedClock q v)) x‖ ≤
      36743 + 640 * densitySlopeBound := by
  have hc := densitySlopeBound_nonneg
  apply norm_fderiv_le_of_lip' (𝕜 := ℝ) (by positivity)
  exact Filter.Eventually.of_forall (fun y ↦ localGuardedClock_fderiv_sub_bound hq v hv y x)

end NCConcave16991.ConeSmooth
