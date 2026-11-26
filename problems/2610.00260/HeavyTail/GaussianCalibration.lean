import HeavyTail.Envelope
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Exponential

/-! Explicit all-budget amplitude calibration for Gaussian transcript testing. -/

namespace HeavyTail.GaussianLower
noncomputable section

def traceAmplitude (G L : ℝ) (T : ℕ) : ℝ := min G (L / (64 * Real.sqrt T))

theorem traceAmplitude_nonneg {G L : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L) (T : ℕ) :
    0 ≤ traceAmplitude G L T := by unfold traceAmplitude; positivity

theorem traceAmplitude_le_G (G L : ℝ) (T : ℕ) : traceAmplitude G L T ≤ G := min_le_left _ _

theorem traceAmplitude_testing {G L : ℝ} {T : ℕ}
    (hG : 0 ≤ G) (hL : 0 < L) (hT : 0 < T) :
    Real.exp ((T : ℝ) * (4 * traceAmplitude G L T ^ 2 / L ^ 2)) ≤ (65 / 64 : ℝ) := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have ha := traceAmplitude_nonneg hG hL.le T
  have hab : traceAmplitude G L T ≤ L / (64 * Real.sqrt T) := min_le_right _ _
  have hexponent : (T : ℝ) * (4 * traceAmplitude G L T ^ 2 / L ^ 2) ≤ (1 / 1024 : ℝ) := by
    calc
      _ ≤ (T : ℝ) * (4 * (L / (64 * Real.sqrt T)) ^ 2 / L ^ 2) := by
        gcongr
      _ = 1 / 1024 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hTr.le]
        field_simp
        <;> ring
  calc
    _ ≤ Real.exp (1 / 1024 : ℝ) := Real.exp_le_exp.mpr hexponent
    _ ≤ 1 / (1 - (1 / 1024 : ℝ)) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    _ ≤ 65 / 64 := by norm_num

theorem traceAmplitude_lower {G L : ℝ} (hG : 0 ≤ G) (_hL : 0 ≤ L) (T : ℕ) :
    (1 / 64 : ℝ) * min G (L / Real.sqrt T) ≤ traceAmplitude G L T := by
  apply le_min
  · have h := mul_le_mul_of_nonneg_left (min_le_left G (L / Real.sqrt T))
      (by norm_num : (0 : ℝ) ≤ 1 / 64)
    nlinarith
  · have h := mul_le_mul_of_nonneg_left (min_le_right G (L / Real.sqrt T))
      (by norm_num : (0 : ℝ) ≤ 1 / 64)
    convert h using 1 <;> ring

theorem traceAmplitude_envelope {μ D G L : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hL : 0 ≤ L) (T : ℕ) :
    (1 / 16384 : ℝ) * envelope μ D (min G (L / Real.sqrt T)) ≤
      envelope μ D (traceAmplitude G L T) / 4 := by
  have hscale := envelope_scale_lower hμ hD
    (show 0 ≤ min G (L / Real.sqrt T) by positivity)
    (by norm_num : (0 : ℝ) ≤ 1 / 64) (by norm_num : (1 / 64 : ℝ) ≤ 1)
  have hm := envelope_mono hμ hD (by positivity) (traceAmplitude_lower hG hL T)
  nlinarith

end
end HeavyTail.GaussianLower
