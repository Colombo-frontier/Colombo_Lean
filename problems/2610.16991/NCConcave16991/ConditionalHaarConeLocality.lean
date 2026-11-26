import NCConcave16991.ConeRecoveryGuard

/-!
# Deterministic flatness criterion for the actual cone oracle

The only unrevealed directions in an unfinished cone block occur through two
bounded probes: the capped source vector and the normalized clock vector.
Small correlations force the actual clock correction and exit gate, including
their gradients, to vanish. This supplies the exact local identity needed by
a reference-oracle coupling.
-/

open scoped InnerProductSpace

namespace NCConcave16991.Haar

noncomputable section

open ConePrimitives ConeRadial ConeClockGap ConeRecovery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def normalizedClockProbe (u : E) : E := (Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ • u

theorem normalizedClockProbe_norm_le (u : E) : ‖normalizedClockProbe u‖ ≤ 1 := by
  have hp : 0 < Real.sqrt (1 + ‖u‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hn : ‖u‖ ≤ Real.sqrt (1 + ‖u‖ ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  rw [normalizedClockProbe, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp]
  calc
    _ ≤ (Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ * Real.sqrt (1 + ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

theorem clock_angle_of_normalized_correlation (v u : E)
    (h : |⟪normalizedClockProbe u, v⟫_ℝ| ≤ 1 / 2) :
    2 * ⟪u, v⟫_ℝ ^ 2 ≤ 1 + ‖u‖ ^ 2 := by
  have hp : 0 < Real.sqrt (1 + ‖u‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hh : |⟪u, v⟫_ℝ| / Real.sqrt (1 + ‖u‖ ^ 2) ≤ 1 / 2 := by
    simpa only [normalizedClockProbe, real_inner_smul_left, abs_mul, abs_inv,
      abs_of_pos hp, div_eq_mul_inv, mul_comm] using h
  have ht := (div_le_iff₀ hp).mp hh
  have ht2 := pow_le_pow_left₀ (abs_nonneg ⟪u, v⟫_ℝ) ht 2
  have hs := Real.sq_sqrt (show 0 ≤ 1 + ‖u‖ ^ 2 by positivity)
  nlinarith [sq_abs ⟪u, v⟫_ℝ, sq_nonneg ⟪u, v⟫_ℝ]

theorem clock_inner_le_perpendicular_sqrt (v u : E) (hv : ‖v‖ = 1)
    (hangle : 2 * ⟪u, v⟫_ℝ ^ 2 ≤ 1 + ‖u‖ ^ 2) {b : ℝ} (hb : 1 ≤ b) :
    ⟪u, v⟫_ℝ ≤ Real.sqrt (b + ‖perpendicular v u‖ ^ 2) := by
  have hd := norm_sq_decomposition v u hv
  have hs := Real.sq_sqrt (show 0 ≤ b + ‖perpendicular v u‖ ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (b + ‖perpendicular v u‖ ^ 2)
  by_contra h
  have ht : Real.sqrt (b + ‖perpendicular v u‖ ^ 2) < ⟪u, v⟫_ℝ := lt_of_not_ge h
  have hp : 0 < (⟪u, v⟫_ℝ - Real.sqrt (b + ‖perpendicular v u‖ ^ 2)) *
      (⟪u, v⟫_ℝ + Real.sqrt (b + ‖perpendicular v u‖ ^ 2)) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

theorem unfinished_clock_argument_nonpos (v z u : E) (hv : ‖v‖ = 1)
    (hz : ⟪zeta z, v⟫_ℝ ≤ 1 / 4)
    (hu : |⟪normalizedClockProbe u, v⟫_ℝ| ≤ 1 / 2) : clockArgument v z u ≤ 0 := by
  rw [clockArgument, latch_zero hz]
  have hh := clock_inner_le_perpendicular_sqrt v u hv
    (clock_angle_of_normalized_correlation v u hu) (b := 1) le_rfl
  linarith

theorem unfinished_clock_value {q : ℝ} (v z u : E) (hv : ‖v‖ = 1)
    (hz : ⟪zeta z, v⟫_ℝ ≤ 1 / 4)
    (hu : |⟪normalizedClockProbe u, v⟫_ℝ| ≤ 1 / 2) :
    clock q v z u = Real.sqrt (1 + ‖u‖ ^ 2) - 1 + ‖u‖ ^ 2 / (2 * q) := by
  change _ - 10 * theta (clockArgument v z u) = _
  rw [theta_zero (unfinished_clock_argument_nonpos v z u hv hz hu)]
  ring

theorem unfinished_clock_z_gradient (v z u : E) (hv : ‖v‖ = 1)
    (hz : ⟪zeta z, v⟫_ℝ ≤ 1 / 4)
    (hu : |⟪normalizedClockProbe u, v⟫_ℝ| ≤ 1 / 2) : clockZGradient v z u = 0 := by
  have ho := omega_zero (show clockArgument v z u ≤ 1 / 4 by
    linarith [unfinished_clock_argument_nonpos v z u hv hz hu])
  simp only [clockZGradient, ho, mul_zero, zero_mul, zero_smul, neg_zero]

theorem unfinished_clock_u_gradient {q : ℝ} (v z u : E) (hv : ‖v‖ = 1)
    (hz : ⟪zeta z, v⟫_ℝ ≤ 1 / 4)
    (hu : |⟪normalizedClockProbe u, v⟫_ℝ| ≤ 1 / 2) :
    clockUGradient q v z u = ((Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ + q⁻¹) • u := by
  have ho := omega_zero (show clockArgument v z u ≤ 1 / 4 by
    linarith [unfinished_clock_argument_nonpos v z u hv hz hu])
  simp only [clockUGradient, ho, mul_zero, zero_smul, sub_zero]

theorem unfinished_gate_argument_nonpos {q : ℝ} (hq : 1 ≤ q) (v u : E) (hv : ‖v‖ = 1)
    (hu : |⟪normalizedClockProbe u, v⟫_ℝ| ≤ 1 / 2) : gateArgument q v u ≤ 0 := by
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  unfold gateArgument
  apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
  have hh := clock_inner_le_perpendicular_sqrt v u hv
    (clock_angle_of_normalized_correlation v u hu) hq2
  linarith

theorem unfinished_gate_value {q : ℝ} (hq : 1 ≤ q) (v u : E) (hv : ‖v‖ = 1)
    (hu : |⟪normalizedClockProbe u, v⟫_ℝ| ≤ 1 / 2) : exitGate q v u = 0 := by
  apply exitStep_zero
  exact (unfinished_gate_argument_nonpos hq v u hv hu).trans (by norm_num)

theorem unfinished_gate_gradient {q : ℝ} (hq : 1 ≤ q) (v u : E) (hv : ‖v‖ = 1)
    (hu : |⟪normalizedClockProbe u, v⟫_ℝ| ≤ 1 / 2) : gateUGradient q v u = 0 := by
  have hd := density_zero_left (show gateArgument q v u - 1 ≤ 1 / 4 by
    linarith [unfinished_gate_argument_nonpos hq v u hv hu])
  simp only [gateUGradient, hd, zero_div, zero_smul]

end

end NCConcave16991.Haar
