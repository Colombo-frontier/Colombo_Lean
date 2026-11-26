import Bilevel.SmallGapMean

/-! The actual sign-dependent potential and global informative-gradient envelope. -/

noncomputable section
namespace Bilevel.SmallGapInstance.Parameters

open scoped RealInnerProductSpace
open SmallGapProfiles SmallGapProfileBounds SmallGapLiftSupport SmallGapThirdBounds

variable (P : Parameters)

def signal (y : LowerSpace) : ℝ :=
  P.μ / P.L * r1 P.S P.δ (y 0) * normal P.δ (y 1) -
    P.μ / P.L ^ 2 * r0 P.S P.R (y 0) * r1 P.S P.δ (y 0)

def signalU (y : LowerSpace) : ℝ :=
  P.μ / P.L * deriv (r1 P.S P.δ) (y 0) * normal P.δ (y 1) -
    P.μ / P.L ^ 2 * (deriv (r0 P.S P.R) (y 0) * r1 P.S P.δ (y 0) +
      r0 P.S P.R (y 0) * deriv (r1 P.S P.δ) (y 0))

def signalS (y : LowerSpace) : ℝ :=
  P.μ / P.L * r1 P.S P.δ (y 0) * deriv (normal P.δ) (y 1)

def signalY (y : LowerSpace) : LowerSpace := pack (P.signalU y) (P.signalS y) 0

def publicLower (x : ℝ) (y : LowerSpace) : ℝ :=
  P.lower 0 x y + P.μ / (2 * P.L ^ 2) * (r1 P.S P.δ (y 0)) ^ 2

theorem lower_sign_decomposition (ω x : ℝ) (y : LowerSpace) (hω : ω ^ 2 = 1) :
    P.lower ω x y = P.publicLower x y + ω * P.signal y := by
  unfold publicLower lower residual signal
  simp only [zero_mul, sub_zero]
  ring_nf
  rw [hω]
  ring

theorem signal_hasGradientAt (y : LowerSpace) : HasGradientAt P.signal (P.signalY y) y := by
  have h0 := p0.hasFDerivAt (x := y)
  have h1 := p1.hasFDerivAt (x := y)
  have hr0 := ((r0_contDiff P.S P.R).differentiable (by norm_num) (y 0)).hasDerivAt.hasFDerivAt.comp y h0
  have hr1 := ((r1_contDiff P.S P.δ).differentiable (by norm_num) (y 0)).hasDerivAt.hasFDerivAt.comp y h0
  have hq := ((normal_contDiff P.δ P.δ_pos).differentiable (by norm_num) (y 1)).hasDerivAt.hasFDerivAt.comp y h1
  have h := ((hr1.const_mul (P.μ / P.L)).mul hq).sub
    ((hr0.const_mul (P.μ / P.L ^ 2)).mul hr1)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h using 1
  ext v
  simp [signalY, signalU, signalS, InnerProductSpace.toDual_apply, Fin.sum_univ_succ]
  ring

theorem lower_gradient_signal_difference (x : ℝ) (y : LowerSpace) :
    P.lowerY 1 x y - P.lowerY (-1) x y = 2 • P.signalY y := by
  ext i
  fin_cases i <;> simp [lowerY, lowerU, lowerS, signalY, signalU, signalS,
    P.residual_deriv, residual] <;> ring

theorem lower_outer_gradient_common (x : ℝ) (y : LowerSpace) :
    P.lowerX 1 x y = P.lowerX (-1) x y := rfl

def signalBound : ℝ := 614 * C ^ 2 * P.μ * (P.S / P.L) * P.δ ^ 2

theorem signalBound_pos : 0 < P.signalBound := by
  have hC := C_pos
  have hμ := P.μ_pos
  have hL := P.L_pos
  have hS := P.S_pos
  have hδ := P.δ_pos
  unfold signalBound
  positivity

theorem signalU_bound (y : LowerSpace) (hsmall : P.S * P.δ ≤ P.L) :
    |P.signalU y| ≤ 613 * C ^ 2 * P.μ * (P.S / P.L) * P.δ ^ 2 := by
  have hC := C_pos
  have hS := P.S_pos
  have hR := P.R_pos
  have hδ := P.δ_pos
  have hL := P.L_pos
  have hμ := P.μ_pos
  have hC2 : C ≤ C ^ 2 := by nlinarith [C_one_le]
  have hf := r1_jet_bounds P.S P.δ (y 0) hS hδ
  have hq := normal_jet_bounds P.δ (y 1) hδ
  by_cases hu : |y 0| ≤ 34 * P.δ
  · have hu2 : (y 0) ^ 2 ≤ 1156 * P.δ ^ 2 := by
      nlinarith [sq_abs (y 0), abs_nonneg (y 0)]
    have hc0 : |r0 P.S P.R (y 0)| ≤ 578 * P.S * P.δ ^ 2 := by
      have hb := r0_local_bound P.S P.R (y 0) hS hR
      have hh := mul_le_mul_of_nonneg_left hu2 hS.le
      nlinarith
    have hc1 : |deriv (r0 P.S P.R) (y 0)| ≤ 34 * P.S * P.δ := by
      have hb := r0_local_deriv_bound P.S P.R (y 0) hS hR
      have hh := mul_le_mul_of_nonneg_left hu hS.le
      nlinarith
    have hp0 : |deriv (r1 P.S P.δ) (y 0) * normal P.δ (y 1)| ≤ C ^ 2 * P.S * P.δ ^ 2 := by
      rw [abs_mul]
      convert mul_le_mul hf.2.1 hq.1 (abs_nonneg _) (by positivity) using 1
      ring
    have hp1 : |deriv (r0 P.S P.R) (y 0) * r1 P.S P.δ (y 0) +
        r0 P.S P.R (y 0) * deriv (r1 P.S P.δ) (y 0)| ≤ 612 * C ^ 2 * P.S ^ 2 * P.δ ^ 3 := by
      have hb0 := mul_le_mul hc1 hf.1 (abs_nonneg _) (by positivity)
      have hb1 := mul_le_mul hc0 hf.2.1 (abs_nonneg _) (by positivity)
      have hh := abs_add (deriv (r0 P.S P.R) (y 0) * r1 P.S P.δ (y 0))
        (r0 P.S P.R (y 0) * deriv (r1 P.S P.δ) (y 0))
      rw [abs_mul, abs_mul] at hh
      have hCmul := mul_le_mul_of_nonneg_right hC2 (show 0 ≤ P.S ^ 2 * P.δ ^ 3 by positivity)
      nlinarith
    have hb0 := mul_le_mul_of_nonneg_left hp0 (div_nonneg hμ.le hL.le)
    have hb1 := mul_le_mul_of_nonneg_left hp1 (div_nonneg hμ.le (sq_nonneg P.L))
    have ht := abs_sub (P.μ / P.L * (deriv (r1 P.S P.δ) (y 0) * normal P.δ (y 1)))
      (P.μ / P.L ^ 2 * (deriv (r0 P.S P.R) (y 0) * r1 P.S P.δ (y 0) +
        r0 P.S P.R (y 0) * deriv (r1 P.S P.δ) (y 0)))
    rw [abs_mul (P.μ / P.L), abs_of_nonneg (div_nonneg hμ.le hL.le), abs_mul (P.μ / P.L ^ 2),
      abs_of_nonneg (div_nonneg hμ.le (sq_nonneg P.L))] at ht
    have hh := mul_le_mul_of_nonneg_left hsmall
      (show 0 ≤ 612 * C ^ 2 * P.μ / P.L ^ 2 * P.S * P.δ ^ 2 by positivity)
    have he : P.signalU y = P.μ / P.L * (deriv (r1 P.S P.δ) (y 0) * normal P.δ (y 1)) -
        P.μ / P.L ^ 2 * (deriv (r0 P.S P.R) (y 0) * r1 P.S P.δ (y 0) +
          r0 P.S P.R (y 0) * deriv (r1 P.S P.δ) (y 0)) := by unfold signalU; ring
    rw [he]
    have hcancel : 612 * C ^ 2 * P.μ / P.L ^ 2 * P.S * P.δ ^ 2 * P.L =
        612 * C ^ 2 * P.μ * (P.S / P.L) * P.δ ^ 2 := by field_simp [hL.ne']; ring
    rw [hcancel] at hh
    ring_nf at hb0 hb1 hh ht ⊢
    linarith only [hb0, hb1, hh, ht]
  · have hzero := r1_zero P.S P.δ (y 0) hδ (le_of_not_ge hu)
    have hd := r1_deriv_zero P.S P.δ (y 0) hδ (le_of_not_ge hu)
    rw [signalU, hzero, hd]
    simp only [mul_zero, zero_mul, add_zero, sub_zero, abs_zero]
    positivity

theorem signalS_bound (y : LowerSpace) :
    |P.signalS y| ≤ C ^ 2 * P.μ * (P.S / P.L) * P.δ ^ 2 := by
  have hμL := div_nonneg P.μ_pos.le P.L_pos.le
  have hf := r1_jet_bounds P.S P.δ (y 0) P.S_pos P.δ_pos
  have hq := normal_jet_bounds P.δ (y 1) P.δ_pos
  have hC := C_pos
  have hS := P.S_pos
  have hp := mul_le_mul hf.1 hq.2.1 (abs_nonneg _) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hp hμL
  rw [signalS, abs_mul, abs_mul, abs_of_nonneg hμL]
  convert hh using 1 <;> ring

theorem signal_gradient_bound (y : LowerSpace) (hsmall : P.S * P.δ ≤ P.L) :
    ‖P.signalY y‖ ≤ P.signalBound := by
  have hU := P.signalU_bound y hsmall
  have hS := P.signalS_bound y
  have hnorm := pack_norm_le (P.signalU y) (P.signalS y) 0
  rw [abs_zero, add_zero] at hnorm
  change ‖pack (P.signalU y) (P.signalS y) 0‖ ≤ _
  dsimp [signalBound]
  nlinarith

theorem signal_gradient_bound_of_scale (y : LowerSpace)
    (hscale : 4096 * C ^ 2 * P.S * P.R ≤ P.L) : ‖P.signalY y‖ ≤ P.signalBound := by
  have hsmall := (P.smallness_of_scale hscale).1.fine
  have hnonneg := mul_nonneg P.S_pos.le P.δ_pos.le
  apply P.signal_gradient_bound
  linarith [P.L_pos]

end Bilevel.SmallGapInstance.Parameters
