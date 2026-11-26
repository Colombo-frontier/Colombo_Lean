import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Explicit `β = 4` arithmetic

The manuscript uses radii `1` and `1/2` and weights `-1/3` and `4/3`.
This file checks the cancellation, the `h³/12` bias constant, and the numeric
second-moment envelope.
-/

namespace NoisyZO

theorem betaFour_weights_sum : (-1 / 3 : ℝ) + 4 / 3 = 1 := by norm_num

theorem betaFour_quadratic_cancellation :
    (-1 / 3 : ℝ) * 1 ^ 2 + (4 / 3) * (1 / 2 : ℝ) ^ 2 = 0 := by
  norm_num

theorem betaFour_bias
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ} (eOuter eInner : E)
    (hOuter : ‖eOuter‖ ≤ h ^ 3 / 6)
    (hInner : ‖eInner‖ ≤ (h / 2) ^ 3 / 6) :
    ‖(-1 / 3 : ℝ) • eOuter + (4 / 3 : ℝ) • eInner‖ ≤ h ^ 3 / 12 := by
  calc
    ‖(-1 / 3 : ℝ) • eOuter + (4 / 3 : ℝ) • eInner‖ ≤
        ‖(-1 / 3 : ℝ) • eOuter‖ + ‖(4 / 3 : ℝ) • eInner‖ := norm_add_le _ _
    _ = (1 / 3 : ℝ) * ‖eOuter‖ + (4 / 3 : ℝ) * ‖eInner‖ := by
      simp [norm_smul]
    _ ≤ (1 / 3 : ℝ) * (h ^ 3 / 6) +
        (4 / 3 : ℝ) * ((h / 2) ^ 3 / 6) := by gcongr
    _ = h ^ 3 / 12 := by ring

theorem betaFour_noise_constant {d h : ℝ} (hh : h ≠ 0) :
    (d / (6 * h)) ^ 2 * (64 * 2 + 2) = 65 * d ^ 2 / (18 * h ^ 2) := by
  field_simp [hh]
  ring

theorem betaFour_secondMoment_envelope {d h : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1) :
    225 * d ^ 2 + 65 * d ^ 2 / (18 * h ^ 2) ≤
      229 * d ^ 2 / h ^ 2 := by
  have hh_sq_pos : 0 < h ^ 2 := sq_pos_of_pos hh0
  have hh_sq_le : h ^ 2 ≤ 1 := by nlinarith
  apply (le_div_iff₀ hh_sq_pos).2
  field_simp [ne_of_gt hh_sq_pos]
  nlinarith

end NoisyZO
