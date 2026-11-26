import NCConcave16991.ConeSmoothRules
import NCConcave16991.ConeSmoothRadial
import NCConcave16991.ConeSmoothRoot
import NCConcave16991.ConeRecoveryBranch

/-! # Actual quantitative cone clock and exit-gate coefficients -/

noncomputable section

namespace NCConcave16991.ConeSmooth

open ConePrimitives ConeRadial ConeClockGap ConeRecovery Set
open scoped InnerProductSpace ContDiff

theorem scalar_deriv_sub_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) {C : ℝ}
    (hbound : ∀ t, |deriv (deriv f) t| ≤ C) (x y : ℝ) :
    |deriv f x - deriv f y| ≤ C * |x - y| := by
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (𝕜 := ℝ)
    (f := deriv f) (fun t _ ↦ hd.differentiable (by simp) t)
    (fun t _ ↦ by simpa only [Real.norm_eq_abs] using hbound t)
    convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

theorem omega_sub_bound (x y : ℝ) : |omega x - omega y| ≤ 2 * |x - y| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (𝕜 := ℝ)
    (f := omega) (fun t _ ↦ (omega_hasDerivAt t).differentiableAt)
    (fun t _ ↦ by rw [(omega_hasDerivAt t).deriv, Real.norm_eq_abs,
      abs_of_nonneg (density_nonneg t)]; exact density_le_two t)
    convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

theorem latch_contDiff : ContDiff ℝ ∞ latch :=
  omega_contDiff.comp (by fun_prop)

theorem exitStep_contDiff : ContDiff ℝ ∞ exitStep :=
  omega_contDiff.comp (by fun_prop)

theorem latch_deriv_sub_bound (x y : ℝ) :
    |deriv latch x - deriv latch y| ≤ (16 * densitySlopeBound) * |x - y| :=
  scalar_deriv_sub_bound latch latch_contDiff latch_second_derivative_bound x y

theorem exitStep_deriv_sub_bound (x y : ℝ) :
    |deriv exitStep x - deriv exitStep y| ≤ densitySlopeBound * |x - y| :=
  scalar_deriv_sub_bound exitStep exitStep_contDiff exitStep_second_derivative_bound x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem rootNorm_derivativeBound {a : ℝ} (ha : 0 < a) :
    DerivativeBound (rootNorm a : E → ℝ) 1 (2 / Real.sqrt a) :=
  ⟨rootNorm_contDiff ha, by norm_num, by positivity, rootNorm_fderiv_norm_le ha,
    rootNorm_fderiv_sub_bound ha⟩

def score (v z : E) : ℝ := ⟪zeta z, v⟫_ℝ

theorem score_fderiv (v z : E) :
    fderiv ℝ (score v) z = (innerSL ℝ v).comp (fderiv ℝ (zeta : E → E) z) := by
  have hh := (innerSL ℝ v).hasFDerivAt.comp z (zeta_differentiable z).hasFDerivAt
  have hf : (fun x : E ↦ ⟪v, zeta x⟫_ℝ) = score v := by funext x; exact real_inner_comm _ _
  change HasFDerivAt (fun x : E ↦ ⟪v, zeta x⟫_ℝ) _ z at hh
  rw [hf] at hh
  exact hh.fderiv

theorem score_derivativeBound (v : E) (hv : ‖v‖ = 1) : DerivativeBound (score v) 1 5 := by
  refine ⟨zeta_contDiff.inner ℝ contDiff_const, by norm_num, by norm_num, ?_, ?_⟩
  · intro z
    rw [score_fderiv]
    have hh := (innerSL ℝ v).opNorm_comp_le (fderiv ℝ (zeta : E → E) z)
    rw [innerSL_apply_norm, hv, one_mul] at hh
    exact hh.trans (zeta_fderiv_norm_le z)
  · intro x y
    rw [score_fderiv, score_fderiv, ← ContinuousLinearMap.comp_sub]
    have hh := (innerSL ℝ v).opNorm_comp_le
      (fderiv ℝ (zeta : E → E) x - fderiv ℝ (zeta : E → E) y)
    rw [innerSL_apply_norm, hv, one_mul] at hh
    exact hh.trans (zeta_fderiv_sub_bound x y)

theorem perpendicularOperator_norm_le (v : E) (hv : ‖v‖ = 1) : ‖perpendicularOperator v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro u
  rw [perpendicularOperator_apply, one_mul]
  have hh := norm_sq_decomposition v u hv
  nlinarith [sq_nonneg ⟪u, v⟫_ℝ, norm_nonneg (perpendicular v u), norm_nonneg u]

abbrev Pair (E : Type*) := WithLp 2 (E × E)

def pairZ : Pair E →L[ℝ] E := WithLp.fstL 2 ℝ E E
def pairU : Pair E →L[ℝ] E := WithLp.sndL 2 ℝ E E

theorem pairZ_norm : ‖pairZ (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro p
  exact (WithLp.norm_fst_le (p := 2) (α := E) (β := E) p).trans_eq (one_mul _).symm

theorem pairU_norm : ‖pairU (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro p
  exact (WithLp.norm_snd_le (p := 2) (α := E) (β := E) p).trans_eq (one_mul _).symm

theorem argument_derivativeBound (v : E) (hv : ‖v‖ = 1) :
    DerivativeBound (fun p : Pair E ↦ clockArgument v p.fst p.snd) 34
      (64 * densitySlopeBound + 162) := by
  have hlinear : DerivativeBound (fun p : Pair E ↦ ⟪p.snd, v⟫_ℝ) 1 0 := by
    have hn := (innerSL ℝ v).opNorm_comp_le (pairU (E := E))
    rw [innerSL_apply_norm, hv, one_mul] at hn
    have hh := DerivativeBound.linear ((innerSL ℝ v).comp (pairU (E := E))) (B := 1) (by norm_num)
      (hn.trans pairU_norm)
    convert hh using 1
    funext p
    exact real_inner_comm _ _
  have hroot := ((rootNorm_derivativeBound (E := E) (by norm_num : (0 : ℝ) < 1)).comp_contraction
    (perpendicularOperator v) (perpendicularOperator_norm_le v hv)).comp_contraction
      (pairU (E := E)) pairU_norm
  norm_num only [Real.sqrt_one, div_one] at hroot
  have hscore := (score_derivativeBound v hv).comp_contraction (pairZ (E := E)) pairZ_norm
  have hlatch := hscore.scalar_comp latch (deriv latch) latch_contDiff
    (fun t ↦ latch_contDiff.differentiable (by simp) t |>.hasDerivAt)
    (by norm_num : (0 : ℝ) ≤ 8) (mul_nonneg (by norm_num) densitySlopeBound_nonneg)
    (fun t ↦ by rw [abs_of_nonneg (latch_deriv_bounds t).1]; exact (latch_deriv_bounds t).2)
    latch_deriv_sub_bound
  have hh := (hlinear.sub hroot).add (hlatch.const_mul 4)
  convert hh using 1 <;> simp [clockArgument, rootNorm, pairU, pairZ, score,
    perpendicularOperator_apply] <;> ring

theorem theta_argument_derivativeBound (v : E) (hv : ‖v‖ = 1) :
    DerivativeBound (fun p : Pair E ↦ theta (clockArgument v p.fst p.snd)) 34
      (64 * densitySlopeBound + 2474) := by
  have hh := (argument_derivativeBound v hv).scalar_comp theta omega theta_contDiff theta_hasDerivAt
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2)
    (fun t ↦ by rw [abs_of_nonneg (omega_nonneg t)]; exact omega_le_one t) omega_sub_bound
  convert hh using 1 <;> ring

theorem exitGate_derivativeBound {q : ℝ} (hq : 0 < q) (v : E) (hv : ‖v‖ = 1) :
    DerivativeBound (exitGate q v) (4 / q) (4 * (densitySlopeBound + 1) / q ^ 2) := by
  have hlinear := DerivativeBound.linear (innerSL ℝ v) (B := 1) (by norm_num)
    (by rw [innerSL_apply_norm, hv])
  have hroot := (rootNorm_derivativeBound (E := E) (sq_pos_of_pos hq)).comp_contraction
    (perpendicularOperator v) (perpendicularOperator_norm_le v hv)
  rw [Real.sqrt_sq hq.le] at hroot
  have hargument : DerivativeBound (gateArgument q v) (2 / q) (2 / q ^ 2) := by
    have hh := (hlinear.sub hroot).const_mul q⁻¹
    convert hh using 1 <;> simp only [gateArgument, rootNorm, perpendicularOperator_apply,
      innerSL_apply_apply, div_eq_mul_inv, abs_inv, abs_of_pos hq]
    · funext u
      unfold gateArgument
      rw [real_inner_comm]
      ring
    · ring
    · ring
  have hh := hargument.scalar_comp exitStep (deriv exitStep) exitStep_contDiff
    (fun t ↦ exitStep_contDiff.differentiable (by simp) t |>.hasDerivAt)
    (by norm_num : (0 : ℝ) ≤ 2) densitySlopeBound_nonneg
    (fun t ↦ by rw [abs_of_nonneg (exitStep_deriv_bounds t).1]; exact (exitStep_deriv_bounds t).2)
    exitStep_deriv_sub_bound
  convert hh using 1
  all_goals try rfl
  all_goals ring

end NCConcave16991.ConeSmooth
