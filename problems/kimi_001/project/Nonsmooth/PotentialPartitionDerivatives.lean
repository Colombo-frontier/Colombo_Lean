import Nonsmooth.PotentialMomentDerivative

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def potentialTiltMean (U : ℝ → ℝ) (t : ℝ) : ℝ := potentialMoment U 1 t / potentialMoment U 0 t

theorem potentialMoment_zero_pos (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) : 0 < potentialMoment U 0 t := by
  have hi : Integrable (fun x => Real.exp (t * x - U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_tilt_polynomial_integrable U s hs hρ hd hmono t 0
  simpa only [potentialMoment, pow_zero, one_mul] using integral_exp_pos hi

theorem potentialTiltMean_eq_integral (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) :
    potentialTiltMean U t = ∫ x : ℝ, x ∂realDensityLaw (fun x => Real.exp (t * x - U x)) := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hwc : Continuous (fun x => Real.exp (t * x - U x)) := by fun_prop
  have hi : Integrable (fun x => Real.exp (t * x - U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_tilt_polynomial_integrable U s hs hρ hd hmono t 0
  rw [realDensityLaw_integral _ hwc.measurable hi (fun x => (Real.exp_pos _).le)]
  simp only [potentialTiltMean, potentialMoment, pow_one, pow_zero, one_mul]

theorem potentialTiltVariance_eq (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) :
    variance (fun x : ℝ => x) (realDensityLaw (fun x => Real.exp (t * x - U x))) =
      potentialMoment U 2 t / potentialMoment U 0 t - (potentialTiltMean U t) ^ 2 := by
  have hprob := strong_potential_tilt_probability_and_memLp U s hs hρ hd hmono t
  letI := hprob.1
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hwc : Continuous (fun x => Real.exp (t * x - U x)) := by fun_prop
  have hi : Integrable (fun x => Real.exp (t * x - U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_tilt_polynomial_integrable U s hs hρ hd hmono t 0
  rw [variance_eq_sub hprob.2, ← potentialTiltMean_eq_integral U s hs hρ hd hmono t]
  have hsq := realDensityLaw_integral _ hwc.measurable hi (fun x => (Real.exp_pos _).le) (fun x : ℝ => x ^ 2)
  change (∫ x : ℝ, x ^ 2 ∂realDensityLaw (fun x => Real.exp (t * x - U x))) -
    potentialTiltMean U t ^ 2 = _
  rw [hsq]
  simp only [potentialMoment, pow_zero, one_mul]

theorem potentialTiltMean_hasDerivAt (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) :
    HasDerivAt (potentialTiltMean U)
      (variance (fun x : ℝ => x) (realDensityLaw (fun x => Real.exp (t * x - U x)))) t := by
  have hZ := (potentialMoment_zero_pos U s hs hρ hd hmono t).ne'
  have h := (potentialMoment_hasDerivAt U s hs hρ hd hmono 1 t).div
    (potentialMoment_hasDerivAt U s hs hρ hd hmono 0 t) hZ
  convert! h using 1
  rw [potentialTiltVariance_eq U s hs hρ hd hmono t, potentialTiltMean]
  field_simp <;> ring

theorem potentialLogPartition_hasDerivAt (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) :
    HasDerivAt (fun r => Real.log (potentialMoment U 0 r)) (potentialTiltMean U t) t :=
  (potentialMoment_hasDerivAt U s hs hρ hd hmono 0 t).log
    (potentialMoment_zero_pos U s hs hρ hd hmono t).ne'

end
end Nonsmooth
