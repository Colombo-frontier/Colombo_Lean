import GradientHessian.Profiles
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Actual oriented-integral profiles in the manuscript. The primitive is globally
defined on the real line; restricting `primitive 1` to nonnegative arguments is
the radial profile q. -/

noncomputable section
open Set MeasureTheory

namespace GradientHessian.IntegralProfiles
open Profiles

def density (a t : ℝ) : ℝ := 1 - step (t-a)
def primitive (a t : ℝ) : ℝ := ∫ v in (0:ℝ)..t, density a v
def evenDensity (a t : ℝ) : ℝ := 1 - step (|t|-a)
def evenPrimitive (a t : ℝ) : ℝ := ∫ v in (0:ℝ)..t, evenDensity a v
def ell₀ (t : ℝ) : ℝ := 4 + evenPrimitive 2 t
def theta (t : ℝ) : ℝ := evenPrimitive 8 t

theorem density_contDiff (a : ℝ) : ContDiff ℝ 3 (density a) :=
  contDiff_const.sub (contDiff_step.comp (contDiff_id.sub contDiff_const))

theorem density_continuous (a : ℝ) : Continuous (density a) := (density_contDiff a).continuous

theorem density_bounds (a t : ℝ) : 0 ≤ density a t ∧ density a t ≤ 1 := by
  have := step_bounds (t-a)
  dsimp [density]; constructor <;> linarith [this.1, this.2]

theorem density_antitone (a : ℝ) : Antitone (density a) := by
  intro t u h
  exact sub_le_sub_left (step_monotone (sub_le_sub_right h a)) 1

theorem primitive_derivative (a t : ℝ) : HasDerivAt (primitive a) (density a t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((density_continuous a).intervalIntegrable _ _)
    ((density_continuous a).stronglyMeasurable.stronglyMeasurableAtFilter)
    (density_continuous a).continuousAt

theorem deriv_primitive (a : ℝ) : deriv (primitive a) = density a :=
  deriv_eq (primitive_derivative a)

theorem primitive_contDiff (a : ℝ) : ContDiff ℝ 4 (primitive a) := by
  rw [show (4 : WithTop ℕ∞) = 3+1 by norm_num, contDiff_succ_iff_deriv, deriv_primitive]
  exact ⟨fun t => (primitive_derivative a t).differentiableAt, by simp, density_contDiff a⟩

theorem primitive_zero (a : ℝ) : primitive a 0 = 0 := by simp [primitive]

theorem primitive_identity {a t : ℝ} (ha : 0 ≤ a) (ht : t ≤ a) : primitive a t = t := by
  unfold primitive
  calc
    (∫ v in (0:ℝ)..t, density a v) = ∫ _ in (0:ℝ)..t, (1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ≤ a := by
        rcases mem_uIcc.mp hv with hv | hv
        · exact hv.2.trans ht
        · exact hv.2.trans ha
      simp [density, step_nonpos (sub_nonpos.mpr hv')]
    _ = t := by simp

private def septicIntegral (t : ℝ) : ℝ := 7*t^5-14*t^6+10*t^7-(5/2)*t^8

private theorem septicIntegral_derivative (t : ℝ) :
    HasDerivAt septicIntegral (septic t) t := by
  convert ((((hasDerivAt_id t).pow 5).const_mul 7).sub
    (((hasDerivAt_id t).pow 6).const_mul 14)).add
    (((hasDerivAt_id t).pow 7).const_mul 10) |>.sub
    (((hasDerivAt_id t).pow 8).const_mul (5/2)) using 1
  dsimp [septicIntegral, septic]; ring

theorem integral_step : (∫ t in (0:ℝ)..1, step t) = 1/2 := by
  have hp : Continuous septic := by unfold septic; fun_prop
  calc
    (∫ t in (0:ℝ)..1, step t) = ∫ t in (0:ℝ)..1, septic t := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), mem_Icc] at ht
      exact step_eq_septic ht.1 ht.2
    _ = septicIntegral 1 - septicIntegral 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => septicIntegral_derivative t)
        (hp.intervalIntegrable _ _)
    _ = 1/2 := by norm_num [septicIntegral]

theorem primitive_at_end {a : ℝ} (ha : 0 ≤ a) : primitive a (a+1) = a+1/2 := by
  have hc := density_continuous a
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a (a+1))
  have htail : (∫ v in a..a+1, density a v) = 1/2 := by
    change (∫ v in a..a+1, (fun s => 1-step s) (v-a)) = _
    rw [intervalIntegral.integral_comp_sub_right (fun s : ℝ => 1-step s) a]
    simp only [sub_self, add_sub_cancel_left]
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (contDiff_step.continuous.intervalIntegrable _ _), integral_step]
    norm_num
  change primitive a a + _ = primitive a (a+1) at hadd
  rw [primitive_identity ha le_rfl, htail] at hadd
  linarith

theorem primitive_plateau {a t : ℝ} (ha : 0 ≤ a) (ht : a+1 ≤ t) :
    primitive a t = a+1/2 := by
  have hc := density_continuous a
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (a+1)) (hc.intervalIntegrable (a+1) t)
  have htail : (∫ v in (a+1)..t, density a v) = 0 := by
    calc
      _ = ∫ _ in (a+1)..t, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        have hv' := (uIcc_of_le ht ▸ hv : v ∈ Icc (a+1) t).1
        simp [density, step_ge_one (by linarith : 1 ≤ v-a)]
      _ = 0 := by simp
  change primitive a (a+1) + _ = primitive a t at hadd
  rw [primitive_at_end ha, htail, add_zero] at hadd
  exact hadd.symm

theorem primitive_monotone (a : ℝ) : Monotone (primitive a) :=
  monotone_of_hasDerivAt_nonneg (primitive_derivative a) (fun t => (density_bounds a t).1)

theorem primitive_nonneg {a t : ℝ} (ht : 0 ≤ t) : 0 ≤ primitive a t := by
  simpa only [primitive_zero] using primitive_monotone a ht

theorem primitive_upper {a t : ℝ} (ha : 0 ≤ a) : primitive a t ≤ a+1/2 := by
  by_cases ht : t ≤ a+1
  · simpa only [primitive_at_end ha] using primitive_monotone a ht
  · exact (primitive_plateau ha (le_of_not_ge ht)).le

theorem primitive_le_self {a t : ℝ} (ht : 0 ≤ t) : primitive a t ≤ t := by
  have h := intervalIntegral.integral_mono (μ := volume) ht
    ((density_continuous a).intervalIntegrable 0 t)
    (continuous_const.intervalIntegrable 0 t) (fun v => (density_bounds a v).2)
  simpa [primitive] using h

theorem density_mul_le_primitive {a t : ℝ} (ht : 0 ≤ t) :
    density a t * t ≤ primitive a t := by
  have h := intervalIntegral.integral_mono_on (μ := volume) ht
    (continuous_const.intervalIntegrable 0 t)
    ((density_continuous a).intervalIntegrable 0 t)
    (fun v hv => density_antitone a hv.2)
  simpa [primitive, mul_comm] using h

theorem evenDensity_continuous (a : ℝ) : Continuous (evenDensity a) :=
  continuous_const.sub (contDiff_step.continuous.comp (continuous_abs.sub continuous_const))

theorem evenPrimitive_derivative (a t : ℝ) :
    HasDerivAt (evenPrimitive a) (evenDensity a t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((evenDensity_continuous a).intervalIntegrable _ _)
    ((evenDensity_continuous a).stronglyMeasurable.stronglyMeasurableAtFilter)
    (evenDensity_continuous a).continuousAt

theorem deriv_evenPrimitive (a : ℝ) : deriv (evenPrimitive a) = evenDensity a :=
  deriv_eq (evenPrimitive_derivative a)

theorem evenDensity_split {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    evenDensity a t = density a t + density a (-t) - 1 := by
  by_cases ht : 0 ≤ t
  · simp [evenDensity, density, abs_of_nonneg ht,
      step_nonpos (by linarith : -t-a ≤ 0)]
  · simp [evenDensity, density, abs_of_neg (lt_of_not_ge ht),
      step_nonpos (by linarith : t-a ≤ 0)]

theorem evenPrimitive_eq {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    evenPrimitive a t = primitive a t - primitive a (-t) - t := by
  have hd : ∀ x : ℝ, HasDerivAt (fun u => primitive a u - primitive a (-u) - u)
      (evenDensity a x) x := by
    intro x
    convert ((primitive_derivative a x).sub
      ((primitive_derivative a (-x)).comp x (hasDerivAt_id x).neg)).sub (hasDerivAt_id x) using 1
    rw [evenDensity_split ha x]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((evenDensity_continuous a).intervalIntegrable 0 t)
  simpa only [primitive_zero, neg_zero, sub_zero, sub_self] using hi

theorem evenPrimitive_contDiff {a : ℝ} (ha : 0 ≤ a) : ContDiff ℝ 4 (evenPrimitive a) := by
  have heq : evenPrimitive a = fun t => primitive a t - primitive a (-t) - t :=
    funext (evenPrimitive_eq ha)
  rw [heq]
  exact ((primitive_contDiff a).sub ((primitive_contDiff a).comp contDiff_id.neg)).sub contDiff_id

theorem evenPrimitive_nonneg_arg {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    evenPrimitive a t = primitive a t := by
  rw [evenPrimitive_eq ha, primitive_identity ha (by linarith : -t ≤ a)]
  ring

theorem evenPrimitive_nonpos_arg {a t : ℝ} (ha : 0 ≤ a) (ht : t ≤ 0) :
    evenPrimitive a t = -primitive a (-t) := by
  rw [evenPrimitive_eq ha, primitive_identity ha (ht.trans ha)]
  ring

theorem evenPrimitive_identity {a t : ℝ} (ha : 0 ≤ a) (ht : |t| ≤ a) :
    evenPrimitive a t = t := by
  rw [evenPrimitive_eq ha,
    primitive_identity ha (le_abs_self t |>.trans ht),
    primitive_identity ha (neg_le_abs t |>.trans ht)]
  ring

theorem evenPrimitive_abs_bound {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    |evenPrimitive a t| ≤ a+1/2 := by
  by_cases ht : 0 ≤ t
  · rw [evenPrimitive_nonneg_arg ha ht, abs_of_nonneg (primitive_nonneg ht)]
    exact primitive_upper ha
  · rw [evenPrimitive_nonpos_arg ha (le_of_not_ge ht), abs_neg,
      abs_of_nonneg (primitive_nonneg (by linarith : 0 ≤ -t))]
    exact primitive_upper ha

theorem evenPrimitive_derivative_bounds (a t : ℝ) :
    0 ≤ deriv (evenPrimitive a) t ∧ deriv (evenPrimitive a) t ≤ 1 := by
  rw [deriv_evenPrimitive]
  exact density_bounds a |t|

theorem ell₀_contDiff : ContDiff ℝ 4 ell₀ :=
  contDiff_const.add (evenPrimitive_contDiff (by norm_num))

theorem theta_contDiff : ContDiff ℝ 4 theta := evenPrimitive_contDiff (by norm_num)

theorem ell₀_derivative (t : ℝ) : HasDerivAt ell₀ (1-step (|t|-2)) t := by
  simpa only [zero_add] using (evenPrimitive_derivative 2 t).const_add 4

theorem theta_derivative (t : ℝ) : HasDerivAt theta (1-step (|t|-8)) t :=
  evenPrimitive_derivative 8 t

theorem ell₀_derivative_bounds (t : ℝ) : 0 ≤ deriv ell₀ t ∧ deriv ell₀ t ≤ 1 := by
  rw [(ell₀_derivative t).deriv]
  exact density_bounds 2 |t|

theorem theta_derivative_bounds (t : ℝ) : 0 ≤ deriv theta t ∧ deriv theta t ≤ 1 :=
  evenPrimitive_derivative_bounds 8 t

theorem ell₀_identity {t : ℝ} (ht : |t| ≤ 2) : ell₀ t = 4+t := by
  unfold ell₀
  rw [evenPrimitive_identity (by norm_num) ht]

theorem ell₀_bounds (t : ℝ) : 3/2 ≤ ell₀ t ∧ ell₀ t ≤ 13/2 := by
  have h := abs_le.mp (evenPrimitive_abs_bound (by norm_num : (0:ℝ) ≤ 2) t)
  dsimp [ell₀]; constructor <;> linarith [h.1, h.2]

theorem theta_identity {t : ℝ} (ht : |t| ≤ 8) : theta t = t :=
  evenPrimitive_identity (by norm_num) ht

theorem theta_abs_bound (t : ℝ) : |theta t| ≤ 17/2 := by
  have h := evenPrimitive_abs_bound (by norm_num : (0:ℝ) ≤ 8) t
  convert h using 1
  norm_num [theta]

end GradientHessian.IntegralProfiles
