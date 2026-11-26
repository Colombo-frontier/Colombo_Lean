import NCConcave16991.ConeRecoveryCertificate
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Derivatives of the literal maximizing branch -/

noncomputable section

namespace NCConcave16991.ConeRecovery

open ConePrimitives ConeRadial ConeClockGap ConeValue
open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Composition

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Z U : F → E} {Z' U' : F →L[ℝ] E} {x : F}

theorem clock_comp_hasFDerivAt {q : ℝ} (hq : 0 < q) (v : E) (hv : ‖v‖ = 1)
    (hZ : HasFDerivAt Z Z' x) (hU : HasFDerivAt U U' x) :
    HasFDerivAt (fun t ↦ clock q v (Z t) (U t))
      ((innerSL ℝ (clockZGradient v (Z x) (U x))).comp Z' +
        (innerSL ℝ (clockUGradient q v (Z x) (U x))).comp U') x := by
  have ht : HasFDerivAt (fun t ↦ ⟪U t, v⟫_ℝ) ((innerSL ℝ v).comp U') x := by
    have hh := (innerSL ℝ v).hasFDerivAt.comp x hU
    change HasFDerivAt (fun t ↦ ⟪v, U t⟫_ℝ) _ x at hh
    simpa only [real_inner_comm v] using hh
  have hinner : HasFDerivAt (fun t ↦ ⟪zeta (Z t), v⟫_ℝ)
      ((innerSL ℝ v).comp ((fderiv ℝ (zeta : E → E) (Z x)).comp Z')) x := by
    have hh := (innerSL ℝ v).hasFDerivAt.comp x ((zeta_differentiable (Z x)).hasFDerivAt.comp x hZ)
    change HasFDerivAt (fun t ↦ ⟪v, zeta (Z t)⟫_ℝ) _ x at hh
    simpa only [real_inner_comm v] using hh
  have hH := (latch_hasDerivAt ⟪zeta (Z x), v⟫_ℝ).comp_hasFDerivAt x hinner
  have ha := (ht.sub ((sqrt_perpendicular_hasFDerivAt (by norm_num : (0 : ℝ) < 1) v (U x) hv).comp x hU)).add
    (hH.const_mul 4)
  have htheta := (theta_hasDerivAt (clockArgument v (Z x) (U x))).comp_hasFDerivAt x ha
  have hquad := ((hasStrictFDerivAt_norm_sq (U x)).hasFDerivAt.comp x hU).mul_const (2 * q)⁻¹
  simp only [← div_eq_mul_inv] at hquad
  have hs := ((sqrt_norm_sq_hasFDerivAt (by norm_num : (0 : ℝ) < 1) (U x)).comp x hU).sub_const 1
  have hh := (hs.add hquad).sub (htheta.const_mul 10)
  refine hh.congr_fderiv ?_
  ext h
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, clockZGradient, clockUGradient, capAdjoint,
    real_inner_smul_left, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    smul_eq_mul]
  field_simp
  ring

end Composition

variable {M : ℕ}

def zProjection (j : Fin (M + 1)) : PrimalBlocks E M →L[ℝ] E :=
  (PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
    (WithLp.fstL 2 ℝ (Blocks E M) (Blocks E M))

def uProjection (j : Fin (M + 1)) : PrimalBlocks E M →L[ℝ] E :=
  (PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
    (WithLp.sndL 2 ℝ (Blocks E M) (Blocks E M))

@[simp] theorem zProjection_apply (j : Fin (M + 1)) (x : PrimalBlocks E M) :
    zProjection j x = x.fst j := rfl

@[simp] theorem uProjection_apply (j : Fin (M + 1)) (x : PrimalBlocks E M) :
    uProjection j x = x.snd j := rfl

def previousGateDerivative (q : ℝ) (v : Fin (M + 1) → E) (u : Blocks E M)
    (j : Fin (M + 1)) : PrimalBlocks E M →L[ℝ] ℝ :=
  if h : j.val = 0 then 0 else
    (innerSL ℝ (gateUGradient q (v ⟨j.val - 1, by omega⟩) (u ⟨j.val - 1, by omega⟩))).comp
      (uProjection ⟨j.val - 1, by omega⟩)

theorem previousGate_comp_hasFDerivAt {q : ℝ} (hq : 0 < q)
    (v : Fin (M + 1) → E) (hv : ∀ j, ‖v j‖ = 1) (x : PrimalBlocks E M) (j : Fin (M + 1)) :
    HasFDerivAt (fun p : PrimalBlocks E M ↦ previousGate q v (fun k ↦ p.snd k) j)
      (previousGateDerivative q v x.snd j) x := by
  unfold previousGate previousGateDerivative
  split
  · exact hasFDerivAt_const (𝕜 := ℝ) 1 x
  · exact (exitGate_hasFDerivAt hq _ _ (hv _)).comp x (uProjection _).hasFDerivAt

set_option backward.isDefEq.respectTransparency false in
theorem source_inner_comp_hasFDerivAt (v a : E) (x : PrimalBlocks E M) (j : Fin (M + 1)) :
    HasFDerivAt (fun p : PrimalBlocks E M ↦ ⟪zeta (p.fst j) - v, a⟫_ℝ)
      ((innerSL ℝ (capAdjoint (x.fst j) a)).comp (zProjection j)) x := by
  have hh := (source_hasFDerivAt_z 1 v (x.fst j) a).comp x (zProjection j).hasFDerivAt
  simp only [one_mul, sourceZGradient, one_smul] at hh
  convert hh using 1
  rfl

theorem summed_gate_derivative (q : ℝ) (v : Fin (M + 1) → E) (z u a : Blocks E M) :
    (∑ j, ⟪zeta (z j) - v j, a j⟫_ℝ • previousGateDerivative q v u j) =
      ∑ j, nextCoefficient v z a j •
        ((innerSL ℝ (gateUGradient q (v j) (u j))).comp (uProjection j)) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc (f := fun j ↦ nextCoefficient v z a j •
    ((innerSL ℝ (gateUGradient q (v j) (u j))).comp (uProjection j)))]
  simp only [previousGateDerivative, Fin.val_zero, ↓reduceDIte, smul_zero, zero_add,
    Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte,
    Nat.add_sub_cancel, nextCoefficient, Fin.val_last, lt_self_iff_false, zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hnext : (j.castSucc : Fin (M + 1)).val + 1 < M + 1 := by simpa using j.succ.isLt
  rw [dif_pos hnext]
  rfl

def branchGradient (q : ℝ) (v : Fin (M + 1) → E) (z u a : Blocks E M) : PrimalBlocks E M :=
  WithLp.toLp 2 (multiplierZBlock q v z u a, multiplierUBlock q v z u a)

theorem branch_hasFDerivAt {q : ℝ} (hq : 0 < q) (v : Fin (M + 1) → E)
    (hv : ∀ j, ‖v j‖ = 1) (x : PrimalBlocks E M) (a : Blocks E M) :
    HasFDerivAt (fun p : PrimalBlocks E M ↦ branch q v p.fst p.snd a)
      (innerSL ℝ (branchGradient q v x.fst x.snd a)) x := by
  have hclock (j : Fin (M + 1)) := clock_comp_hasFDerivAt hq (v j) (hv j)
    (zProjection j).hasFDerivAt (uProjection j).hasFDerivAt (x := x)
  have hguard (j : Fin (M + 1)) := (guard_hasGradientAt 3000 (x.fst j)).hasFDerivAt.comp x
    (zProjection j).hasFDerivAt
  have hsource (j : Fin (M + 1)) := (previousGate_comp_hasFDerivAt hq v hv x j).mul
    (source_inner_comp_hasFDerivAt (v j) (a j) x j)
  have hterm (j : Fin (M + 1)) := ((hclock j).add (hguard j)).add (hsource j)
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hterm j)
  have hf : (fun p : PrimalBlocks E M ↦ ∑ j, (clock q (v j) (p.fst j) (p.snd j) +
      ConeRadial.guard 3000 (p.fst j) + previousGate q v (fun j ↦ p.snd j) j *
        ⟪zeta (p.fst j) - v j, a j⟫_ℝ)) = (fun p ↦ branch q v p.fst p.snd a) := by
    funext p
    exact (branch_sum q v p.fst p.snd a).symm
  change HasFDerivAt (fun p : PrimalBlocks E M ↦ ∑ j, (clock q (v j) (p.fst j) (p.snd j) +
      ConeRadial.guard 3000 (p.fst j) + previousGate q v (fun j ↦ p.snd j) j *
        ⟪zeta (p.fst j) - v j, a j⟫_ℝ)) _ x at hh
  rw [hf] at hh
  refine hh.congr_fderiv ?_
  simp only [Finset.sum_add_distrib]
  rw [summed_gate_derivative]
  ext h
  simp only [ContinuousLinearMap.sum_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, branchGradient, WithLp.prod_inner_apply, multiplierZBlock,
    multiplierUBlock, PiLp.inner_apply, zProjection_apply, uProjection_apply,
    inner_add_left, real_inner_smul_left, sourceZGradient, smul_eq_mul]
  simp_rw [(guard_hasGradientAt 3000 _).gradient]
  simp only [InnerProductSpace.toDual_apply_apply]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [WithLp.fst, WithLp.snd]
  ring

theorem branch_hasGradientAt {q : ℝ} (hq : 0 < q) (v : Fin (M + 1) → E)
    (hv : ∀ j, ‖v j‖ = 1) (x : PrimalBlocks E M) (a : Blocks E M) :
    HasGradientAt (fun p : PrimalBlocks E M ↦ branch q v p.fst p.snd a)
      (branchGradient q v x.fst x.snd a) x := branch_hasFDerivAt hq v hv x a

theorem source_recovery_from_branch_gradient {q : ℝ} (hq : 16 ≤ q)
    (v : Fin (M + 1) → E) (hv : ∀ j, ‖v j‖ = 1) (x : PrimalBlocks E M)
    (a : Blocks E M) (ha : ‖a‖ ≤ 1)
    (hmax : ∀ b ∈ Metric.closedBall (0 : Blocks E M) 1,
      branch q v x.fst x.snd b ≤ branch q v x.fst x.snd a)
    (hsmall : ‖gradient (fun p : PrimalBlocks E M ↦ branch q v p.fst p.snd a) x‖ ≤ 1 / 1000) :
    ∀ j, x.fst j = v j := by
  have he := (branch_hasGradientAt (by linarith : 0 < q) v hv x a).gradient
  rw [he] at hsmall
  have hz : ‖multiplierZBlock q v x.fst x.snd a‖ ≤ 1 / 1000 :=
    (WithLp.norm_fst_le (p := 2) (α := Blocks E M) (β := Blocks E M) (branchGradient q v x.fst x.snd a)).trans hsmall
  have hu : ‖multiplierUBlock q v x.fst x.snd a‖ ≤ 1 / 1000 :=
    (WithLp.norm_snd_le (p := 2) (α := Blocks E M) (β := Blocks E M) (branchGradient q v x.fst x.snd a)).trans hsmall
  have hr := source_recovery_from_maximizing_branch hq v x.fst x.snd a hv ha hmax hz hu
  exact fun j ↦ (hr.2 j).1

/-- Small gradient at an actual maximizer of the actual finite-sum dual
problem recovers every hidden mean. No derivative or value identity is a
hypothesis of this theorem. -/
theorem source_recovery_from_actual_average {n : ℕ} (hn : 0 < n) {R q : ℝ}
    (hR : 0 < R) (hq : 16 ≤ q) (w : Fin n → Fin (M + 1) → E)
    (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j)) (x : PrimalBlocks E M) (y : Blocks E M)
    (hy : y ∈ Metric.closedBall 0 R)
    (hmax : ∀ b ∈ Metric.closedBall (0 : Blocks E M) R,
      (n : ℝ)⁻¹ * ∑ i, component R q w i x.fst x.snd b ≤
        (n : ℝ)⁻¹ * ∑ i, component R q w i x.fst x.snd y)
    (hsmall : ‖gradient (fun p : PrimalBlocks E M ↦
      (n : ℝ)⁻¹ * ∑ i, component R q w i p.fst p.snd y) x‖ ≤ 1 / 1000) :
    ∀ j, x.fst j = sourceMean w j := by
  have hyn : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have ha : ‖R⁻¹ • y‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have hh := mul_le_mul_of_nonneg_left hyn (inv_nonneg.mpr hR.le)
    simpa only [inv_mul_cancel₀ hR.ne'] using hh
  have hfun : (fun p : PrimalBlocks E M ↦ (n : ℝ)⁻¹ * ∑ i, component R q w i p.fst p.snd y) =
      (fun p ↦ branch q (sourceMean w) p.fst p.snd (R⁻¹ • y)) := by
    funext p
    exact component_average_eq_branch hn R q w p.fst p.snd y
  rw [hfun] at hsmall
  apply source_recovery_from_branch_gradient hq (sourceMean w) (sourceMean_unit hn w hw) x
    (R⁻¹ • y) ha _ hsmall
  intro b hb
  have hbn : ‖b‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  have hRb : R • b ∈ Metric.closedBall 0 R := by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR]
    nlinarith
  have hh := hmax (R • b) hRb
  simp only [component_average_eq_branch hn, smul_smul, inv_mul_cancel₀ hR.ne', one_smul] at hh
  exact hh

end NCConcave16991.ConeRecovery
