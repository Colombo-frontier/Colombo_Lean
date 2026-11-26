import FreshGradientMinimax.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Real.Pi.Bounds

/-! The exact Gaussian primitive Θ in Appendix C, defined by its improper
Lebesgue integral. Its values and actual derivative are established here. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory Set

def coreDensity (t : ℝ) : ℝ := Real.exp (-(t ^ 2) / 2)
def coreTheta (t : ℝ) : ℝ := ∫ s in Iic t, coreDensity s
def coreThetaMass : ℝ := Real.sqrt (2 * Real.pi)

theorem coreDensity_pos (t : ℝ) : 0 < coreDensity t := Real.exp_pos _

theorem coreDensity_continuous : Continuous coreDensity := by
  unfold coreDensity
  fun_prop

theorem coreDensity_integrable : Integrable coreDensity := by
  convert integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) using 1
  funext t
  unfold coreDensity
  congr 1
  ring

theorem coreDensity_integral : (∫ t, coreDensity t) = coreThetaMass := by
  have h := integral_gaussian (1 / 2 : ℝ)
  convert h using 1
  · congr 1
    funext t
    unfold coreDensity
    congr 1
    ring
  · unfold coreThetaMass
    congr 1
    ring

theorem coreTheta_pos (t : ℝ) : 0 < coreTheta t := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun s => (coreDensity_pos s).le))
    coreDensity_integrable.integrableOn).mpr
  have hs : Function.support coreDensity = univ := by
    ext s
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (coreDensity_pos s).ne'
  simp [hs, Real.volume_Iic]

theorem coreTheta_le_mass (t : ℝ) : coreTheta t ≤ coreThetaMass := by
  rw [← coreDensity_integral]
  exact setIntegral_le_integral coreDensity_integrable
    (Filter.Eventually.of_forall (fun s => (coreDensity_pos s).le))

theorem coreThetaMass_lt_three : coreThetaMass < 3 := by
  unfold coreThetaMass
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  nlinarith [Real.pi_lt_four, Real.sqrt_nonneg (2 * Real.pi)]

theorem coreTheta_lt_three (t : ℝ) : coreTheta t < 3 :=
  (coreTheta_le_mass t).trans_lt coreThetaMass_lt_three

theorem coreTheta_sub (a b : ℝ) : coreTheta b - coreTheta a = ∫ s in a..b, coreDensity s :=
  intervalIntegral.integral_Iic_sub_Iic coreDensity_integrable.integrableOn
    coreDensity_integrable.integrableOn

theorem coreTheta_hasDerivAt (t : ℝ) : HasDerivAt coreTheta (coreDensity t) t := by
  have he : coreTheta = fun x => (∫ s in (0 : ℝ)..x, coreDensity s) + coreTheta 0 := by
    funext x
    linarith only [coreTheta_sub 0 x]
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right
    (coreDensity_continuous.intervalIntegrable 0 t)
    coreDensity_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    coreDensity_continuous.continuousAt).add_const _

theorem coreTheta_deriv (t : ℝ) : deriv coreTheta t = coreDensity t :=
  (coreTheta_hasDerivAt t).deriv

theorem coreTheta_continuous : Continuous coreTheta :=
  (show Differentiable ℝ coreTheta from fun t => (coreTheta_hasDerivAt t).differentiableAt).continuous

theorem coreDensity_lower_on_unit {t : ℝ} (ht : |t| ≤ 1) :
    Real.exp (-(1 / 2 : ℝ)) ≤ coreDensity t := by
  apply Real.exp_le_exp.mpr
  have hs : t ^ 2 ≤ 1 := by
    nlinarith [sq_abs t, mul_self_le_mul_self (abs_nonneg t) ht]
  linarith

theorem coreDensity_le_one (t : ℝ) : coreDensity t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg t]

end FreshGradientMinimax
