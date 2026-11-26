import Smoothness2601.ChainProfiles
import Smoothness2601.CutoffBounds
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! Identification of the convenient finite-endpoint primitive with the
source's integral from negative infinity, as an actual Lebesgue set integral. -/
noncomputable section
namespace Smoothness2601.ChainProfiles
open Cutoffs MeasureTheory Set

theorem zeta_integrable : Integrable zeta :=
  zeta_continuous.integrable_of_hasCompactSupport zeta_compact

theorem zeta_integral_left_zero : (∫ u in Iic (-2 : ℝ), zeta u) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro u hu
  apply zeta_zero_far
  have ha := neg_le_abs u
  change u ≤ -2 at hu
  linarith

theorem profile_eq_source_integral (M t : ℝ) :
    profile M t = M*(∫ u in Iic t, zeta u) := by
  have h := intervalIntegral.integral_Iic_sub_Iic (μ := volume) (f := zeta) (a := -2) (b := t)
    (zeta_integrable.integrableOn (s := Iic (-2 : ℝ)))
    (zeta_integrable.integrableOn (s := Iic t))
  rw [zeta_integral_left_zero,sub_zero] at h
  unfold profile
  rw [h]

end Smoothness2601.ChainProfiles
