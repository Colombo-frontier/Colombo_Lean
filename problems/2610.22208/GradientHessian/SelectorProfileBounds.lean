import GradientHessian.Profiles
import GradientHessian.LatchProfiles
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Relative derivative bounds for the literal septic selector profile.
The first two derivatives vanish sufficiently rapidly at both endpoints to
yield normalized Bernoulli-score estimates, including at the flat seams. -/

namespace GradientHessian.SelectorProfileBounds
open Profiles
noncomputable section

def varianceRoot (p : ℝ) : ℝ := Real.sqrt (p*(1-p))

theorem septic_factor (t : ℝ) :
    septic t = t^4*(1+4*(1-t)+10*(1-t)^2+20*(1-t)^3) := by unfold septic; ring

theorem septic_lower {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) : t^4 ≤ septic t := by
  rw [septic_factor]
  have htc : 0 ≤ 1-t := sub_nonneg.mpr ht₁
  have h : 0 ≤ 4*(1-t)+10*(1-t)^2+20*(1-t)^3 := by positivity
  nlinarith [mul_nonneg (pow_nonneg ht 4) h]

theorem one_sub_septic_lower {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    (1-t)^4 ≤ 1-septic t := by
  have h := septic_lower (sub_nonneg.mpr ht₁) (by linarith : 1-t ≤ 1)
  have he := septic_reflection t
  linarith

theorem septic_variance_lower {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    t^2*(1-t)^2 ≤ varianceRoot (septic t) := by
  have hS := septic_lower ht ht₁
  have hSc := one_sub_septic_lower ht ht₁
  apply Real.le_sqrt_of_sq_le
  calc
    (t^2*(1-t)^2)^2 = t^4*(1-t)^4 := by ring
    _ ≤ septic t*(1-septic t) := mul_le_mul hS hSc (by positivity)
      ((pow_nonneg ht 4).trans hS)

theorem septic_first_relative {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    |septic₁ t| ≤ 140*varianceRoot (septic t) := by
  have htc : 0 ≤ 1-t := sub_nonneg.mpr ht₁
  have hprod : t*(1-t) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left (by linarith : 1-t ≤ 1) ht).trans (by simpa using ht₁)
  rw [septic₁_factored, abs_of_nonneg (by positivity)]
  calc
    140*t^3*(1-t)^3 = 140*(t*(1-t))^3 := by ring
    _ ≤ 140*(t*(1-t))^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (mul_nonneg ht htc) hprod (by norm_num : 2 ≤ 3)) (by norm_num)
    _ = 140*(t^2*(1-t)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (septic_variance_lower ht ht₁) (by norm_num)

theorem septic_second_relative {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    |septic₂ t| ≤ 420*varianceRoot (septic t) := by
  have hf : septic₂ t = 420*(t^2*(1-t)^2)*(1-2*t) := by unfold septic₂; ring
  have habs : |1-2*t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [hf, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 420*(t^2*(1-t)^2))]
  calc
    _ ≤ 420*(t^2*(1-t)^2)*1 := mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ 420*varianceRoot (septic t) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left (septic_variance_lower ht ht₁) (by norm_num)

theorem septic_third_bound {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) : |septic₃ t| ≤ 840 := by
  have hf : septic₃ t = 840*(t*(1-t))*(1-5*t+5*t^2) := by unfold septic₃; ring
  have hp : 0 ≤ t*(1-t) := mul_nonneg ht (sub_nonneg.mpr ht₁)
  have hp₁ : t*(1-t) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left (by linarith : 1-t ≤ 1) ht).trans (by simpa using ht₁)
  have habs : |1-5*t+5*t^2| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (2*t-1)]
  rw [hf, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hp)]
  calc
    _ ≤ 840*(t*(1-t))*1 := mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ 840 := by nlinarith

theorem step_first_relative (t : ℝ) : |step₁ t| ≤ 140*varianceRoot (step t) := by
  by_cases ht : t ≤ 0
  · simp [step, step₁, ht, varianceRoot]
  by_cases ht₁ : t ≤ 1
  · simpa only [step, step₁, if_neg ht, if_pos ht₁] using
      septic_first_relative (le_of_not_ge ht) ht₁
  · simp [step, step₁, ht, ht₁, varianceRoot]

theorem step_second_relative (t : ℝ) : |step₂ t| ≤ 420*varianceRoot (step t) := by
  by_cases ht : t ≤ 0
  · simp [step, step₂, ht, varianceRoot]
  by_cases ht₁ : t ≤ 1
  · simpa only [step, step₂, if_neg ht, if_pos ht₁] using
      septic_second_relative (le_of_not_ge ht) ht₁
  · simp [step, step₂, ht, ht₁, varianceRoot]

theorem step_third_bound (t : ℝ) : |step₃ t| ≤ 840 := by
  by_cases ht : t ≤ 0
  · simp [step₃, ht]
  by_cases ht₁ : t ≤ 1
  · simpa only [step₃, if_neg ht, if_pos ht₁] using
      septic_third_bound (le_of_not_ge ht) ht₁
  · simp [step₃, ht, ht₁]

theorem varpi_first_relative (t : ℝ) :
    |deriv varpi t| ≤ 1680*varianceRoot (varpi t) := by
  rw [(LatchProfiles.varpi_derivative t).deriv, abs_mul]
  norm_num
  have h := mul_le_mul_of_nonneg_left (step_first_relative (12*(t-2/3))) (by norm_num : (0:ℝ) ≤ 12)
  simpa only [varpi, ← mul_assoc, show (12:ℝ)*140 = 1680 by norm_num] using h

theorem varpi_second_derivative (t : ℝ) :
    HasDerivAt (deriv varpi) (144*step₂ (12*(t-2/3))) t := by
  have he : deriv varpi = fun u => 12*step₁ (12*(u-2/3)) :=
    funext (fun u => (LatchProfiles.varpi_derivative u).deriv)
  rw [he]
  convert ((step₁_derivative (12*(t-2/3))).comp t
    (((hasDerivAt_id t).sub_const (2/3)).const_mul 12)).const_mul 12 using 1
  ring

theorem varpi_second_relative (t : ℝ) :
    |deriv (deriv varpi) t| ≤ 60480*varianceRoot (varpi t) := by
  rw [(varpi_second_derivative t).deriv, abs_mul]
  norm_num
  have h := mul_le_mul_of_nonneg_left (step_second_relative (12*(t-2/3)))
    (by norm_num : (0:ℝ) ≤ 144)
  simpa only [varpi, ← mul_assoc, show (144:ℝ)*420 = 60480 by norm_num] using h

end
end GradientHessian.SelectorProfileBounds
