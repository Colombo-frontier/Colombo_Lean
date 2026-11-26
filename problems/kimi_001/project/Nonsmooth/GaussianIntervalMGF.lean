import Nonsmooth.IntervalPotentialEvents

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def standardGaussianPotential (x : ℝ) : ℝ := x ^ 2 / 2 + Real.log (Real.sqrt (2 * Real.pi))

theorem standardGaussianPotential_hasDerivAt (x : ℝ) : HasDerivAt standardGaussianPotential x x := by
  convert! (((hasDerivAt_id x).pow 2).div_const 2).add_const (Real.log (Real.sqrt (2 * Real.pi))) using 1 <;>
    norm_num [id_eq] <;> ring

theorem standardGaussianPotential_density (x : ℝ) :
    Real.exp (-standardGaussianPotential x) = gaussianPDFReal 0 1 x := by
  have hp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have he : -standardGaussianPotential x = -(x ^ 2 / 2) - Real.log (Real.sqrt (2 * Real.pi)) := by
    unfold standardGaussianPotential
    ring
  rw [he, Real.exp_sub, Real.exp_log hp]
  simp [gaussianPDFReal, neg_div, div_eq_mul_inv, mul_comm]

theorem standardGaussian_interval_potential_law (a b : ℝ) :
    intervalDensityLaw (fun x => Real.exp (-standardGaussianPotential x)) a b =
      (gaussianReal 0 1)[|Icc a b] := by
  simp_rw [standardGaussianPotential_density]
  rw [intervalDensityLaw_eq_cond_withDensity]
  change (volume.withDensity (gaussianPDF 0 1))[|Icc a b] = _
  rw [← gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0)]

theorem standardGaussian_interval_condition_zero {a b : ℝ} (hab : ¬a < b) :
    (gaussianReal 0 1)[|Icc a b] = 0 := by
  apply cond_eq_zero_of_meas_eq_zero
  rcases lt_or_eq_of_le (le_of_not_gt hab) with h | h
  · rw [Icc_eq_empty (not_le.mpr h), measure_empty]
  · subst b
    rw [Icc_self]
    exact gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : NNReal) ≠ 0) (measure_singleton a)

/-- Every finite-interval truncation of the actual standard Gaussian has centered
MGF bounded by exp(t^2/2). Empty and singleton intervals are also handled. -/
theorem standardGaussian_interval_centered_mgf (a b t : ℝ) :
    let Q := (gaussianReal 0 1)[|Icc a b]
    (∫ x, Real.exp (t * (x - ∫ y : ℝ, y ∂Q)) ∂Q) ≤ Real.exp (t ^ 2 / 2) := by
  dsimp only
  by_cases hab : a < b
  · have hU : Continuous standardGaussianPotential :=
      continuous_iff_continuousAt.mpr (fun x => (standardGaussianPotential_hasDerivAt x).continuousAt)
    have hm : MonotoneOn (fun x : ℝ => x - (1 : ℝ) * x) (Icc a b) := by
      intro x hx y hy hxy
      simp
    have h := interval_potential_centered_mgf standardGaussianPotential (fun x => x) hU continuous_id
      hab (by norm_num : (0 : ℝ) < 1) (fun x _ => standardGaussianPotential_hasDerivAt x) hm t
    try dsimp only at h
    simpa only [standardGaussian_interval_potential_law, mul_one] using h
  · rw [standardGaussian_interval_condition_zero hab]
    simp only [integral_zero_measure]
    exact (Real.exp_pos _).le

theorem standardGaussian_interval_centered_exp_integrable (a b t : ℝ) :
    let Q := (gaussianReal 0 1)[|Icc a b]
    Integrable (fun x => Real.exp (t * (x - ∫ y : ℝ, y ∂Q))) Q := by
  dsimp only
  by_cases hab : a < b
  · have hU : Continuous standardGaussianPotential :=
      continuous_iff_continuousAt.mpr (fun x => (standardGaussianPotential_hasDerivAt x).continuousAt)
    have h := interval_potential_centered_exp_integrable standardGaussianPotential hU hab t
    try dsimp only at h
    simpa only [standardGaussian_interval_potential_law] using h
  · rw [standardGaussian_interval_condition_zero hab]
    exact integrable_zero_measure

end
end Nonsmooth
