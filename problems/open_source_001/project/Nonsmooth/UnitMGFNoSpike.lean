import Nonsmooth.ScalarMGFTails
import Nonsmooth.NoSpikeSmooth

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- A universal numeric no-spike constant for any unit-subgaussian observable
whose squared derivative is controlled by the actual potential curvature. -/
theorem unit_mgf_no_spike_quantile (U s v h r : ℝ → ℝ)
    (hs : Continuous s) (hv : Continuous v) (hr : Continuous r)
    (hd : ∀ x, HasDerivAt U (s x) x) (hsd : ∀ x, HasDerivAt s (v x) x)
    (hhd : ∀ x, HasDerivAt h (r x) x) (hcontrol : ∀ x, (r x) ^ 2 ≤ v x)
    (hi : Integrable (fun x => Real.exp (-U x)))
    (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t * h x)) (realDensityLaw (fun x => Real.exp (-U x))))
    (hb : ∀ t : ℝ, (∫ x, Real.exp (t * h x) ∂realDensityLaw (fun x => Real.exp (-U x))) ≤ Real.exp (t ^ 2 / 2))
    (y : ℝ) :
    (h y) ^ 2 ≤ 36 * (1 + Real.log (1 /
      min ((realDensityLaw (fun x => Real.exp (-U x))).real (Iic y))
        ((realDensityLaw (fun x => Real.exp (-U x))).real (Ioi y)))) := by
  let Q := realDensityLaw (fun x => Real.exp (-U x))
  letI : IsProbabilityMeasure Q := realDensityLaw_probability _ hi
    (fun _ => (Real.exp_pos _).le) (integral_exp_pos hi)
  have hmono : Monotone s := monotone_of_hasDerivAt_nonneg hsd
    (fun x => (sq_nonneg (r x)).trans (hcontrol x))
  have ht (t : ℝ) (ht : 0 ≤ t) : Q.real {x | t ≤ |h x|} ≤ 2 * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    have hh := scalar_unit_mgf_absolute_tail Q h he hb t ht
    rwa [show -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 by ring]
  have hn := no_spike_uniform_log_quantile U s v h r hs hv hr hd hsd hhd hmono hcontrol hi
    (by norm_num : (0 : ℝ) < 1 / 2) ht y
  let q := min (Q.real (Iic y)) (Q.real (Ioi y))
  have hp := realDensityLaw_halfline_positive U hi y
  have hq : 0 < q := lt_min hp.1 hp.2
  have hq1 : q ≤ 1 := (min_le_left _ _).trans measureReal_le_one
  have hL : 0 ≤ Real.log (1 / q) := Real.log_nonneg ((one_le_div hq).mpr hq1)
  have hlog : |Real.log (4 : ℝ)| ≤ 3 := by
    rw [abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  change (h y) ^ 2 ≤ 36 * (1 + Real.log (1 / q))
  change (h y) ^ 2 ≤ (4 + (4 / (1 / 2 : ℝ)) * (|Real.log (2 * 2 : ℝ)| + 1)) *
    (1 + Real.log (1 / q)) at hn
  rw [show (4 / (1 / 2 : ℝ)) = 8 by norm_num, show (2 : ℝ) * 2 = 4 by norm_num] at hn
  have hc : 4 + 8 * (|Real.log (4 : ℝ)| + 1) ≤ 36 := by linarith
  have hfactor : 0 ≤ 1 + Real.log (1 / q) := by linarith
  exact hn.trans (mul_le_mul_of_nonneg_right hc hfactor)

end
end Nonsmooth
