import NCConcave16991.ConeValueComponents
import NCConcave16991.ConeRecoveryGuard

/-! # The active residual creates a unit gradient barrier

The multiplier below is the actual normalized residual. The companion dual
ball theorem proves that every maximizing dual variable has this multiplier
whenever the residual is nonzero.
-/

noncomputable section

namespace NCConcave16991.ConeRecovery

open ConePrimitives ConeRadial ConeClockGap ConeValue
open scoped InnerProductSpace BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : ℕ}

theorem capAdjoint_identity {z : E} (hz : ‖z‖ < 2) (a : E) : capAdjoint z a = a := by
  have hd : HasFDerivAt (zeta : E → E) (ContinuousLinearMap.id ℝ E) z := by
    apply (hasFDerivAt_id (𝕜 := ℝ) z).congr_of_eventuallyEq
    have hn : ∀ᶠ x : E in 𝓝 z, ‖x‖ < 2 := (isOpen_lt continuous_norm continuous_const).mem_nhds hz
    filter_upwards [hn] with x hx
    exact zeta_identity hx.le
  rw [capAdjoint, hd.fderiv, ContinuousLinearMap.adjoint_id]
  rfl

theorem clockZ_residual_inner_nonneg (v z u : E) (hv : ‖v‖ = 1) (hz : ‖z‖ < 2) :
    0 ≤ ⟪clockZGradient v z u, z - v⟫_ℝ := by
  have hcap := zeta_identity hz.le
  rw [clockZGradient, hcap, capAdjoint_identity hz, real_inner_smul_left,
    inner_sub_right, real_inner_comm z v, real_inner_self_eq_norm_sq, hv]
  by_cases ht : ⟪z, v⟫_ℝ ≤ 1
  · have ho := omega_nonneg (clockArgument v z u)
    have hd := density_nonneg (4 * ⟪z, v⟫_ℝ - 1)
    have hp : 0 ≤ 160 * omega (clockArgument v z u) * density (4 * ⟪z, v⟫_ℝ - 1) := by positivity
    nlinarith
  · rw [density_zero_right (by linarith : (7 / 8 : ℝ) ≤ 4 * ⟪z, v⟫_ℝ - 1)]
    simp

theorem guard_residual_inner_nonneg {A : ℝ} (hA : 0 ≤ A) (v z : E) (hv : ‖v‖ = 1) :
    0 ≤ ⟪gradient (ConeRadial.guard A) z, z - v⟫_ℝ := by
  rw [(guard_hasGradientAt A z).gradient, radialMap, real_inner_smul_left,
    inner_sub_right, real_inner_self_eq_norm_sq]
  by_cases hz : ‖z‖ ≤ 3 / 2
  · rw [guardSlope_zero hz]
    simp
  · have hi := real_inner_le_norm z v
    rw [hv, mul_one] at hi
    have hn : 0 ≤ ‖z‖ ^ 2 - ⟪z, v⟫_ℝ := by nlinarith [norm_nonneg z]
    exact mul_nonneg (div_nonneg (guardSlope_nonneg hA _) (norm_nonneg z)) hn

def normalizedResidual (q : ℝ) (v : Fin (M + 1) → E) (z u : Blocks E M) : Blocks E M :=
  ‖residual q v z u‖⁻¹ • residual q v z u

def canonicalZBlock (q : ℝ) (v : Fin (M + 1) → E) (z u : Blocks E M) : Blocks E M :=
  WithLp.toLp 2 (fun j ↦ gradient (ConeRadial.guard 3000) (z j) +
    clockZGradient (v j) (z j) (u j) +
      sourceZGradient (previousGate q v (fun j ↦ u j) j) (z j) (normalizedResidual q v z u j))

theorem normalizedResidual_norm {q : ℝ} {v : Fin (M + 1) → E} {z u : Blocks E M}
    (hr : residual q v z u ≠ 0) : ‖normalizedResidual q v z u‖ = 1 := by
  have hn : 0 < ‖residual q v z u‖ := norm_pos_iff.mpr hr
  simp only [normalizedResidual, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']

theorem canonicalZBlock_inner_ge_one {q : ℝ} {v : Fin (M + 1) → E} {z u : Blocks E M}
    (hv : ∀ j, ‖v j‖ = 1) (hz : ∀ j, ‖z j‖ < 2)
    (hg : ∀ j, previousGate q v (fun j ↦ u j) j = 0 ∨
      previousGate q v (fun j ↦ u j) j = 1)
    (hr : residual q v z u ≠ 0) :
    1 ≤ ⟪canonicalZBlock q v z u, normalizedResidual q v z u⟫_ℝ := by
  have hn : 0 < ‖residual q v z u‖ := norm_pos_iff.mpr hr
  have hblock (j : Fin (M + 1)) :
      ‖normalizedResidual q v z u j‖ ^ 2 ≤
        ⟪canonicalZBlock q v z u j, normalizedResidual q v z u j⟫_ℝ := by
    have hc := clockZ_residual_inner_nonneg (v j) (z j) (u j) (hv j) (hz j)
    have hguard := guard_residual_inner_nonneg (by norm_num : (0 : ℝ) ≤ 3000) (v j) (z j) (hv j)
    rcases hg j with hgj | hgj
    · simp [normalizedResidual, ConeValue.residual, hgj]
    · have he : normalizedResidual q v z u j =
          ‖residual q v z u‖⁻¹ • (z j - v j) := by
        simp [normalizedResidual, ConeValue.residual, hgj, zeta_identity (hz j).le]
      simp only [canonicalZBlock, PiLp.toLp_apply, sourceZGradient, hgj, one_smul,
        capAdjoint_identity (hz j), inner_add_left, real_inner_self_eq_norm_sq]
      rw [he, real_inner_smul_right, real_inner_smul_right]
      nlinarith [mul_nonneg (inv_nonneg.mpr hn.le) hc, mul_nonneg (inv_nonneg.mpr hn.le) hguard]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hblock j)
  rw [← PiLp.norm_sq_eq_of_L2, normalizedResidual_norm hr, one_pow,
    ← PiLp.inner_apply] at hs
  exact hs

/-- A nonzero residual cannot coexist with a small full source-block vector
after guard localization and binary-gate separation. -/
theorem canonicalZBlock_norm_ge_one {q : ℝ} {v : Fin (M + 1) → E} {z u : Blocks E M}
    (hv : ∀ j, ‖v j‖ = 1) (hz : ∀ j, ‖z j‖ < 2)
    (hg : ∀ j, previousGate q v (fun j ↦ u j) j = 0 ∨
      previousGate q v (fun j ↦ u j) j = 1)
    (hr : residual q v z u ≠ 0) : 1 ≤ ‖canonicalZBlock q v z u‖ := by
  have hi := real_inner_le_norm (canonicalZBlock q v z u) (normalizedResidual q v z u)
  rw [normalizedResidual_norm hr, mul_one] at hi
  exact (canonicalZBlock_inner_ge_one hv hz hg hr).trans hi

end NCConcave16991.ConeRecovery
