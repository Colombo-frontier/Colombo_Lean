import NCConcave16991.ConeRecoveryDifferential
import Mathlib.Tactic.Module

/-! # Binary exit gates for small concrete clock-gradient blocks -/

noncomputable section

namespace NCConcave16991.ConeRecovery

open ConePrimitives ConeRadial ConeClockGap
open scoped InnerProductSpace

/-- The numerical part of the partial-gate exclusion. Its hypotheses are
coordinates of the concrete clock and gate gradients, rather than a
stationarity certificate assumed for the constructed primal value. -/
theorem partial_gate_scalar_impossible {q t r s sp sq α d : ℝ}
    (hq : 16 ≤ q) (hr : 0 ≤ r) (hs : 0 < s) (hsp : 0 < sp) (hsq : 0 < sq)
    (hsp2 : sp ^ 2 = 1 + r ^ 2) (hsq2 : sq ^ 2 = q ^ 2 + r ^ 2)
    (hξ : 1 < (t - sq) / q ∧ (t - sq) / q < 2)
    (ht : t / s ≤ 1) (hα : |α| ≤ 4) (hd : 0 ≤ d ∧ d ≤ 2)
    (hparallel : |t / s + t / q - 10 + α * d / q| ≤ 1 / 1000)
    (hperp : |1 / s + 1 / q + 10 / sp - α * d / (q * sq)| * r ≤ 1 / 1000) :
    False := by
  have hq0 : 0 < q := by linarith
  have had : |α * d| ≤ 8 := by
    rw [abs_mul, abs_of_nonneg hd.1]
    exact (mul_le_mul hα hd.2 hd.1 (by norm_num)).trans (by norm_num)
  have had' : α * d ≤ 8 := (le_abs_self _).trans had
  have hsqge : q ≤ sq := by nlinarith
  have he : α * d / (q * sq) ≤ 1 / q := by
    apply (div_le_div_iff₀ (mul_pos hq0 hsq) hq0).mpr
    nlinarith [mul_le_mul_of_nonneg_left (had'.trans (by linarith : 8 ≤ sq)) hq0.le]
  have hc : 10 / sp ≤ 1 / s + 1 / q + 10 / sp - α * d / (q * sq) := by
    linarith [one_div_nonneg.mpr hs.le]
  have hpr : (10 * r) / sp ≤ 1 / 1000 := by
    calc
      (10 * r) / sp = (10 / sp) * r := by ring
      _ ≤ (1 / s + 1 / q + 10 / sp - α * d / (q * sq)) * r :=
        mul_le_mul_of_nonneg_right hc hr
      _ ≤ |1 / s + 1 / q + 10 / sp - α * d / (q * sq)| * r :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hr
      _ ≤ _ := hperp
  have hpr' := (div_le_iff₀ hsp).mp hpr
  have hr1 : r < 1 := by
    by_contra h
    have hrge : 1 ≤ r := le_of_not_gt h
    have hsp_le : sp ≤ 2 * r := by nlinarith
    nlinarith
  have hsq_le : sq ≤ 2 * q := by nlinarith [sq_nonneg r]
  have htq : t / q < 4 := by
    apply (div_lt_iff₀ hq0).mpr
    have hh := (div_lt_iff₀ hq0).mp hξ.2
    linarith
  have hadq : α * d / q ≤ 1 / 2 := by
    apply (div_le_iff₀ hq0).mpr
    linarith
  have hlo := (abs_le.mp hparallel).1
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem partial_gate_argument {q : ℝ} (v u : E)
    (hg : 0 < exitGate q v u ∧ exitGate q v u < 1) :
    1 < gateArgument q v u ∧ gateArgument q v u < 2 := by
  constructor
  · by_contra h
    have hz := exitStep_zero (le_of_not_gt h)
    change exitGate q v u = 0 at hz
    linarith [hg.1]
  · by_contra h
    have ho := exitStep_one (le_of_not_gt h)
    change exitGate q v u = 1 at ho
    linarith [hg.2]

theorem partial_gate_clock_flat {q : ℝ} (hq : 1 ≤ q) (v z u : E)
    (hg : 0 < exitGate q v u ∧ exitGate q v u < 1) :
    omega (clockArgument v z u) = 1 := by
  have hq0 : 0 < q := by linarith
  have hξ := (partial_gate_argument v u hg).1
  change 1 < (⟪u, v⟫_ℝ - Real.sqrt (q ^ 2 + ‖perpendicular v u‖ ^ 2)) / q at hξ
  have ht := (lt_div_iff₀ hq0).mp hξ
  have hroot : Real.sqrt (1 + ‖perpendicular v u‖ ^ 2) ≤
      Real.sqrt (q ^ 2 + ‖perpendicular v u‖ ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  apply omega_one
  unfold clockArgument
  linarith [latch_nonneg ⟪zeta z, v⟫_ℝ]

theorem concrete_block_decomposition {q : ℝ} (v z u : E) (α : ℝ)
    (hf : omega (clockArgument v z u) = 1) :
    clockUGradient q v z u + α • gateUGradient q v u =
      (⟪u, v⟫_ℝ / Real.sqrt (1 + ‖u‖ ^ 2) + ⟪u, v⟫_ℝ / q - 10 +
        α * density (gateArgument q v u - 1) / q) • v +
      (1 / Real.sqrt (1 + ‖u‖ ^ 2) + 1 / q +
        10 / Real.sqrt (1 + ‖perpendicular v u‖ ^ 2) -
        α * density (gateArgument q v u - 1) /
          (q * Real.sqrt (q ^ 2 + ‖perpendicular v u‖ ^ 2))) • perpendicular v u := by
  have hu : u = ⟪u, v⟫_ℝ • v + perpendicular v u := by
    unfold perpendicular
    abel
  unfold clockUGradient gateUGradient
  rw [hf]
  conv_lhs => arg 1; arg 1; arg 2; rw [hu]
  simp only [div_eq_mul_inv, mul_inv_rev]
  module

theorem orthogonal_block_inner (v p : E) (hv : ‖v‖ = 1) (hp : ⟪p, v⟫_ℝ = 0)
    (A B : ℝ) : ⟪A • v + B • p, v⟫_ℝ = A := by
  simp [inner_add_left, real_inner_smul_left, hp, hv]

theorem orthogonal_block_perp_norm (v p : E) (hv : ‖v‖ = 1)
    (hp : ⟪p, v⟫_ℝ = 0) (A B : ℝ) :
    |B| * ‖p‖ ≤ ‖A • v + B • p‖ := by
  have hperp : perpendicular v (A • v + B • p) = B • p := by
    rw [perpendicular, orthogonal_block_inner v p hv hp]
    abel
  have hh := norm_sq_decomposition v (A • v + B • p) hv
  rw [hperp, norm_smul, Real.norm_eq_abs] at hh
  nlinarith [sq_nonneg ⟪A • v + B • p, v⟫_ℝ, norm_nonneg (A • v + B • p),
    mul_nonneg (abs_nonneg B) (norm_nonneg p)]

/-- A small literal clock-gradient block with any permitted adjacent-source
coefficient has a binary exit gate. The derivative formulas used here were
proved from the actual `clock` and `exitGate` functions in the companion file. -/
theorem binary_gate_of_small_concrete_block {q : ℝ} (hq : 16 ≤ q)
    (v z u : E) (hv : ‖v‖ = 1) (α : ℝ) (hα : |α| ≤ 4)
    (hsmall : ‖clockUGradient q v z u + α • gateUGradient q v u‖ ≤ 1 / 1000) :
    exitGate q v u = 0 ∨ exitGate q v u = 1 := by
  by_contra h
  have hb := exitGate_bounds q v u
  have hg : 0 < exitGate q v u ∧ exitGate q v u < 1 := by
    push_neg at h
    exact ⟨lt_of_le_of_ne hb.1 h.1.symm, lt_of_le_of_ne hb.2 h.2⟩
  have hf := partial_gate_clock_flat (by linarith : 1 ≤ q) v z u hg
  let A := ⟪u, v⟫_ℝ / Real.sqrt (1 + ‖u‖ ^ 2) + ⟪u, v⟫_ℝ / q - 10 +
    α * density (gateArgument q v u - 1) / q
  let B := 1 / Real.sqrt (1 + ‖u‖ ^ 2) + 1 / q +
    10 / Real.sqrt (1 + ‖perpendicular v u‖ ^ 2) -
      α * density (gateArgument q v u - 1) /
        (q * Real.sqrt (q ^ 2 + ‖perpendicular v u‖ ^ 2))
  have hdecomp := concrete_block_decomposition (q := q) v z u α hf
  change _ = A • v + B • perpendicular v u at hdecomp
  rw [hdecomp] at hsmall
  have hparallel : |A| ≤ 1 / 1000 := by
    have hh := abs_real_inner_le_norm (A • v + B • perpendicular v u) v
    rw [orthogonal_block_inner v _ hv (perpendicular_inner v u hv), hv, mul_one] at hh
    exact hh.trans hsmall
  have hperp := (orthogonal_block_perp_norm v _ hv (perpendicular_inner v u hv) A B).trans hsmall
  have ht : ⟪u, v⟫_ℝ / Real.sqrt (1 + ‖u‖ ^ 2) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (1 + ‖u‖ ^ 2))).mpr
    have hi := real_inner_le_norm u v
    rw [hv, mul_one] at hi
    have hn : ‖u‖ ≤ Real.sqrt (1 + ‖u‖ ^ 2) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 1 + ‖u‖ ^ 2 by positivity),
        Real.sqrt_nonneg (1 + ‖u‖ ^ 2), norm_nonneg u]
    exact (hi.trans hn).trans (by simp)
  have hq0 : 0 < q := by linarith
  exact partial_gate_scalar_impossible hq (norm_nonneg _) (by positivity) (by positivity)
    (by positivity)
    (Real.sq_sqrt (by positivity)) (Real.sq_sqrt (by positivity))
    (partial_gate_argument v u hg) ht hα ⟨density_nonneg _, density_le_two _⟩ hparallel hperp

end NCConcave16991.ConeRecovery
