import Nonsmooth.NoSpikeProbability
import Mathlib.Probability.CDF

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem no_spike_cdf_quantile (U s v h r : ℝ → ℝ)
    (hs : Continuous s) (hv : Continuous v) (hr : Continuous r)
    (hd : ∀ x, HasDerivAt U (s x) x) (hsd : ∀ x, HasDerivAt s (v x) x)
    (hhd : ∀ x, HasDerivAt h (r x) x) (hmono : Monotone s)
    (hcontrol : ∀ x, (r x) ^ 2 ≤ v x)
    (hi : Integrable (fun x => Real.exp (-U x))) {c C : ℝ} (hc : 0 < c)
    (htail : ∀ t : ℝ, 0 ≤ t →
      (realDensityLaw (fun x => Real.exp (-U x))).real {x | t ≤ |h x|} ≤ C * Real.exp (-c * t ^ 2)) :
    ∀ y : ℝ, (h y) ^ 2 ≤ (4 + (4 / c) * (|Real.log (2 * C)| + 1)) *
      (1 + Real.log (1 /
        min (cdf (realDensityLaw (fun x => Real.exp (-U x))) y)
          (1 - cdf (realDensityLaw (fun x => Real.exp (-U x))) y))) := by
  letI : IsProbabilityMeasure (realDensityLaw (fun x => Real.exp (-U x))) :=
    realDensityLaw_probability _ hi (fun x => (Real.exp_pos _).le) (integral_exp_pos hi)
  intro y
  have hright : (realDensityLaw (fun x => Real.exp (-U x))).real (Ioi y) =
      1 - cdf (realDensityLaw (fun x => Real.exp (-U x))) y := by
    rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, cdf_eq_real]
  simpa only [hright, cdf_eq_real] using
    no_spike_uniform_log_quantile U s v h r hs hv hr hd hsd hhd hmono hcontrol hi hc htail y

/-- A single constant depending only on the tail parameters works for every
smooth density and regression satisfying the no-spike hypotheses. Convexity of
the potential follows internally from the derivative-square control. -/
theorem smooth_no_spike_constant {c C : ℝ} (hc : 0 < c) :
    ∃ A : ℝ, 0 < A ∧ ∀ (U h : ℝ → ℝ), ContDiff ℝ 2 U → ContDiff ℝ 1 h →
      Integrable (fun x => Real.exp (-U x)) →
      (∀ x, (deriv h x) ^ 2 ≤ deriv (deriv U) x) →
      (∀ t : ℝ, 0 ≤ t →
        (realDensityLaw (fun x => Real.exp (-U x))).real {x | t ≤ |h x|} ≤ C * Real.exp (-c * t ^ 2)) →
      ∀ y : ℝ, (h y) ^ 2 ≤ A * (1 + Real.log (1 /
        min (cdf (realDensityLaw (fun x => Real.exp (-U x))) y)
          (1 - cdf (realDensityLaw (fun x => Real.exp (-U x))) y))) := by
  refine ⟨4 + (4 / c) * (|Real.log (2 * C)| + 1), by positivity, ?_⟩
  intro U h hU hh hi hcontrol htail
  have hU' : ContDiff ℝ 1 (deriv U) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) U from hU)).2.2
  have hd (x : ℝ) : HasDerivAt U (deriv U x) x := (hU.differentiable (by norm_num) x).hasDerivAt
  have hsd (x : ℝ) : HasDerivAt (deriv U) (deriv (deriv U) x) x :=
    (hU'.differentiable_one x).hasDerivAt
  have hhd (x : ℝ) : HasDerivAt h (deriv h x) x := (hh.differentiable_one x).hasDerivAt
  have hmono : Monotone (deriv U) := monotone_of_hasDerivAt_nonneg hsd
    (fun x => (sq_nonneg (deriv h x)).trans (hcontrol x))
  exact no_spike_cdf_quantile U (deriv U) (deriv (deriv U)) h (deriv h)
    (hU.continuous_deriv (by norm_num)) (hU'.continuous_deriv (by norm_num)) (hh.continuous_deriv (by norm_num))
    hd hsd hhd hmono hcontrol hi hc htail

end
end Nonsmooth
