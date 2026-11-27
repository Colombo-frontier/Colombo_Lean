import Nonsmooth.NoSpikeLevelMass
import Nonsmooth.RealDensityEventMass

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem no_spike_quantile_mass (U s v h r : ℝ → ℝ)
    (hs : Continuous s) (hv : Continuous v) (hr : Continuous r)
    (hd : ∀ x, HasDerivAt U (s x) x) (hsd : ∀ x, HasDerivAt s (v x) x)
    (hhd : ∀ x, HasDerivAt h (r x) x) (hmono : Monotone s)
    (hcontrol : ∀ x, (r x) ^ 2 ≤ v x)
    (hi : Integrable (fun x => Real.exp (-U x))) {y : ℝ} (hy : 2 ≤ |h y|) :
    min ((realDensityLaw (fun x => Real.exp (-U x))).real (Iic y))
      ((realDensityLaw (fun x => Real.exp (-U x))).real (Ioi y)) ≤
      2 * (realDensityLaw (fun x => Real.exp (-U x))).real {x | |h y| / 2 ≤ |h x|} := by
  have hw0 (x : ℝ) : 0 ≤ Real.exp (-U x) := (Real.exp_pos _).le
  have hZ : 0 < ∫ x, Real.exp (-U x) := integral_exp_pos hi
  have hh : Continuous h := continuous_iff_continuousAt.mpr (fun x => (hhd x).continuousAt)
  rw [realDensityLaw_event_mass _ hi hw0 _ measurableSet_Iic,
    realDensityLaw_event_mass _ hi hw0 _ measurableSet_Ioi,
    realDensityLaw_event_mass _ hi hw0 _ (measurableSet_le measurable_const hh.abs.measurable),
    min_div_div_right hZ.le, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right
    (no_spike_absolute_level_mass U s v h r hs hv hr hd hsd hhd hmono hcontrol hi hy) hZ.le

theorem no_spike_quantile_exponential (U s v h r : ℝ → ℝ)
    (hs : Continuous s) (hv : Continuous v) (hr : Continuous r)
    (hd : ∀ x, HasDerivAt U (s x) x) (hsd : ∀ x, HasDerivAt s (v x) x)
    (hhd : ∀ x, HasDerivAt h (r x) x) (hmono : Monotone s)
    (hcontrol : ∀ x, (r x) ^ 2 ≤ v x)
    (hi : Integrable (fun x => Real.exp (-U x))) (c C : ℝ)
    (htail : ∀ t : ℝ, 0 ≤ t →
      (realDensityLaw (fun x => Real.exp (-U x))).real {x | t ≤ |h x|} ≤ C * Real.exp (-c * t ^ 2))
    {y : ℝ} (hy : 2 ≤ |h y|) :
    min ((realDensityLaw (fun x => Real.exp (-U x))).real (Iic y))
      ((realDensityLaw (fun x => Real.exp (-U x))).real (Ioi y)) ≤
      (2 * C) * Real.exp (-(c / 4) * (h y) ^ 2) := by
  have hb := no_spike_quantile_mass U s v h r hs hv hr hd hsd hhd hmono hcontrol hi hy
  have ht := htail (|h y| / 2) (by positivity)
  have he : -c * (|h y| / 2) ^ 2 = -(c / 4) * (h y) ^ 2 := by rw [div_pow, sq_abs]; ring
  rw [he] at ht
  linarith

/-- The smooth no-spike bound for the actual normalized density. The constant
is explicit, and both quantile tails are strictly positive. -/
theorem no_spike_log_quantile (U s v h r : ℝ → ℝ)
    (hs : Continuous s) (hv : Continuous v) (hr : Continuous r)
    (hd : ∀ x, HasDerivAt U (s x) x) (hsd : ∀ x, HasDerivAt s (v x) x)
    (hhd : ∀ x, HasDerivAt h (r x) x) (hmono : Monotone s)
    (hcontrol : ∀ x, (r x) ^ 2 ≤ v x)
    (hi : Integrable (fun x => Real.exp (-U x))) {c C : ℝ} (hc : 0 < c)
    (htail : ∀ t : ℝ, 0 ≤ t →
      (realDensityLaw (fun x => Real.exp (-U x))).real {x | t ≤ |h x|} ≤ C * Real.exp (-c * t ^ 2))
    (y : ℝ) :
    (h y) ^ 2 ≤ 4 + (4 / c) * (Real.log (2 * C) + Real.log (1 /
      min ((realDensityLaw (fun x => Real.exp (-U x))).real (Iic y))
        ((realDensityLaw (fun x => Real.exp (-U x))).real (Ioi y)))) := by
  have hw0 (x : ℝ) : 0 ≤ Real.exp (-U x) := (Real.exp_pos _).le
  letI : IsProbabilityMeasure (realDensityLaw (fun x => Real.exp (-U x))) :=
    realDensityLaw_probability _ hi hw0 (integral_exp_pos hi)
  have hC : 1 ≤ C := by
    have hz := htail 0 le_rfl
    have hA : {x : ℝ | 0 ≤ |h x|} = univ := by ext x; simp
    simpa only [hA, measureReal_univ_eq_one, zero_pow (by decide : 2 ≠ 0),
      mul_zero, Real.exp_zero, mul_one] using hz
  let q := min ((realDensityLaw (fun x => Real.exp (-U x))).real (Iic y))
    ((realDensityLaw (fun x => Real.exp (-U x))).real (Ioi y))
  have hpositive := realDensityLaw_halfline_positive U hi y
  have hq : 0 < q := lt_min hpositive.1 hpositive.2
  have hq1 : q ≤ 1 := (min_le_left _ _).trans measureReal_le_one
  have hL : 0 ≤ Real.log (1 / q) := Real.log_nonneg ((one_le_div hq).mpr hq1)
  have hLC : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
  change (h y) ^ 2 ≤ 4 + (4 / c) * (Real.log (2 * C) + Real.log (1 / q))
  by_cases hy : 2 ≤ |h y|
  · have he := no_spike_quantile_exponential U s v h r hs hv hr hd hsd hhd hmono hcontrol hi c C htail hy
    have hlog := Real.log_le_log hq he
    rw [Real.log_mul (by positivity : 2 * C ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlog
    have hbig : (h y) ^ 2 ≤ (4 / c) * (Real.log (2 * C) + Real.log (1 / q)) := by
      rw [one_div, Real.log_inv, div_mul_eq_mul_div]
      apply (le_div_iff₀ hc).mpr
      nlinarith [hlog]
    linarith
  · have habs : |h y| < 2 := lt_of_not_ge hy
    have hnonneg := mul_nonneg (by positivity : 0 ≤ 4 / c) (add_nonneg hLC hL)
    nlinarith [sq_abs (h y), abs_nonneg (h y)]

theorem no_spike_uniform_log_quantile (U s v h r : ℝ → ℝ)
    (hs : Continuous s) (hv : Continuous v) (hr : Continuous r)
    (hd : ∀ x, HasDerivAt U (s x) x) (hsd : ∀ x, HasDerivAt s (v x) x)
    (hhd : ∀ x, HasDerivAt h (r x) x) (hmono : Monotone s)
    (hcontrol : ∀ x, (r x) ^ 2 ≤ v x)
    (hi : Integrable (fun x => Real.exp (-U x))) {c C : ℝ} (hc : 0 < c)
    (htail : ∀ t : ℝ, 0 ≤ t →
      (realDensityLaw (fun x => Real.exp (-U x))).real {x | t ≤ |h x|} ≤ C * Real.exp (-c * t ^ 2)) :
    ∀ y : ℝ, (h y) ^ 2 ≤ (4 + (4 / c) * (|Real.log (2 * C)| + 1)) *
      (1 + Real.log (1 /
        min ((realDensityLaw (fun x => Real.exp (-U x))).real (Iic y))
          ((realDensityLaw (fun x => Real.exp (-U x))).real (Ioi y)))) := by
  intro y
  letI : IsProbabilityMeasure (realDensityLaw (fun x => Real.exp (-U x))) :=
    realDensityLaw_probability _ hi (fun x => (Real.exp_pos _).le) (integral_exp_pos hi)
  have hb := no_spike_log_quantile U s v h r hs hv hr hd hsd hhd hmono hcontrol hi hc htail y
  let q := min ((realDensityLaw (fun x => Real.exp (-U x))).real (Iic y))
    ((realDensityLaw (fun x => Real.exp (-U x))).real (Ioi y))
  have hpositive := realDensityLaw_halfline_positive U hi y
  have hq : 0 < q := lt_min hpositive.1 hpositive.2
  have hq1 : q ≤ 1 := (min_le_left _ _).trans measureReal_le_one
  have hL : 0 ≤ Real.log (1 / q) := Real.log_nonneg ((one_le_div hq).mpr hq1)
  have hK : 0 ≤ 4 / c := by positivity
  change (h y) ^ 2 ≤ (4 + (4 / c) * (|Real.log (2 * C)| + 1)) * (1 + Real.log (1 / q))
  change (h y) ^ 2 ≤ 4 + (4 / c) * (Real.log (2 * C) + Real.log (1 / q)) at hb
  have he := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (2 * C))) hK
  nlinarith [mul_nonneg hL hK,
    mul_nonneg hL (mul_nonneg hK (abs_nonneg (Real.log (2 * C))))]

end
end Nonsmooth
