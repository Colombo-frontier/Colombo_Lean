import Nonsmooth.GaussianSelectionRank
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def rankPowerLaw (n : ℕ) : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioc 0 1)).withDensity (fun p => (ENNReal.ofReal p) ^ n)

theorem rankPower_integrable_iff (n : ℕ) (f : ℝ → ℝ) :
    Integrable f (rankPowerLaw n) ↔
      Integrable (fun p => p ^ n * f p) ((volume : Measure ℝ).restrict (Ioc 0 1)) := by
  have hw : Measurable (fun p : ℝ => (ENNReal.ofReal p) ^ n) := measurable_id.ennreal_ofReal.pow_const n
  rw [rankPowerLaw, integrable_withDensity_iff_integrable_smul' hw
    (Eventually.of_forall (fun _ => ENNReal.pow_lt_top ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with p hp
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hp.1.le, smul_eq_mul]

theorem rankPower_integral (n : ℕ) (f : ℝ → ℝ) :
    (∫ p, f p ∂rankPowerLaw n) = ∫ p in Ioc (0 : ℝ) 1, p ^ n * f p := by
  have hw : Measurable (fun p : ℝ => (ENNReal.ofReal p) ^ n) := measurable_id.ennreal_ofReal.pow_const n
  rw [rankPowerLaw, integral_withDensity_eq_integral_toReal_smul hw
    (Eventually.of_forall (fun _ => ENNReal.pow_lt_top ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with p hp
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hp.1.le, smul_eq_mul]

theorem unit_interval_pow_integrable (n : ℕ) :
    Integrable (fun p : ℝ => p ^ n) ((volume : Measure ℝ).restrict (Ioc 0 1)) :=
  (continuous_pow n).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem unit_interval_pow_integral (n : ℕ) :
    (∫ p in Ioc (0 : ℝ) 1, p ^ n) = 1 / ((n : ℝ) + 1) := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_pow]
  simp

theorem rankPower_inverse_tail_first (m : ℕ) :
    Integrable (fun p : ℝ => (1 - p) / p ^ 2) (rankPowerLaw (m + 2)) ∧
      (∫ p : ℝ, (1 - p) / p ^ 2 ∂rankPowerLaw (m + 2)) =
        1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  have hpoly : (fun p : ℝ => p ^ (m + 2) * ((1 - p) / p ^ 2)) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun p => p ^ m - p ^ (m + 1)) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with p hp
    simp only [pow_add, pow_one]
    field_simp [(ne_of_gt hp.1)]
    <;> ring
  have hi : Integrable (fun p : ℝ => p ^ m - p ^ (m + 1)) (volume.restrict (Ioc 0 1)) :=
    (unit_interval_pow_integrable m).sub (unit_interval_pow_integrable (m + 1))
  constructor
  · rw [rankPower_integrable_iff]
    exact hi.congr hpoly.symm
  · rw [rankPower_integral, integral_congr_ae hpoly,
      integral_sub (unit_interval_pow_integrable m) (unit_interval_pow_integrable (m + 1)),
      unit_interval_pow_integral, unit_interval_pow_integral]
    push_cast
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    <;> ring
    <;> simp_all

theorem rankPower_inverse_tail_second (m : ℕ) :
    Integrable (fun p : ℝ => ((1 - p) / p) ^ 2) (rankPowerLaw (m + 2)) ∧
      (∫ p : ℝ, ((1 - p) / p) ^ 2 ∂rankPowerLaw (m + 2)) =
        2 / (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3)) := by
  have hpoly : (fun p : ℝ => p ^ (m + 2) * (((1 - p) / p) ^ 2)) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun p => (p ^ m - 2 * p ^ (m + 1)) + p ^ (m + 2)) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with p hp
    simp only [pow_add, pow_one]
    field_simp [(ne_of_gt hp.1)]
    <;> ring
  have hiSub : Integrable (fun p : ℝ => p ^ m - 2 * p ^ (m + 1)) (volume.restrict (Ioc 0 1)) :=
    (unit_interval_pow_integrable m).sub ((unit_interval_pow_integrable (m + 1)).const_mul 2)
  have hi : Integrable (fun p : ℝ => (p ^ m - 2 * p ^ (m + 1)) + p ^ (m + 2))
      (volume.restrict (Ioc 0 1)) := hiSub.add (unit_interval_pow_integrable (m + 2))
  constructor
  · rw [rankPower_integrable_iff]
    exact hi.congr hpoly.symm
  · rw [rankPower_integral, integral_congr_ae hpoly,
      integral_add hiSub (unit_interval_pow_integrable (m + 2)),
      integral_sub (unit_interval_pow_integrable m) ((unit_interval_pow_integrable (m + 1)).const_mul 2),
      integral_const_mul]
    simp only [unit_interval_pow_integral]
    push_cast
    field_simp
    <;> ring

end
end Nonsmooth
