import Nonsmooth.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic

open MeasureTheory ProbabilityTheory Filter Function
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem standardGaussian_mgf (t : ℝ) : mgf id (gaussianReal 0 1) t = Real.exp (t ^ 2 / 2) := by
  simpa only [zero_mul, NNReal.coe_one, one_mul, zero_add] using
    mgf_gaussianReal (X := id) (p := gaussianReal 0 1) (μ := 0) (v := 1) Measure.map_id t

theorem standardGaussian_exp_integrable (t : ℝ) :
    Integrable (fun z : ℝ => Real.exp (t * z)) (gaussianReal 0 1) := by
  by_contra hn
  have hz := integral_undef hn
  change mgf id (gaussianReal 0 1) t = 0 at hz
  rw [standardGaussian_mgf] at hz
  exact (Real.exp_ne_zero _) hz

theorem standardGaussian_integrableExpSet : integrableExpSet id (gaussianReal 0 1) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact standardGaussian_exp_integrable t

theorem standardGaussian_power_integrable (n : ℕ) :
    Integrable (fun z : ℝ => z ^ n) (gaussianReal 0 1) := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
    rw [standardGaussian_integrableExpSet, interior_univ]
    exact Set.mem_univ _
  exact integrable_pow_of_mem_interior_integrableExpSet h0 n

theorem standardGaussian_mgf_hasDerivAt (t : ℝ) :
    HasDerivAt (mgf id (gaussianReal 0 1)) (Real.exp (t ^ 2 / 2) * t) t := by
  have he : mgf id (gaussianReal 0 1) = fun u => Real.exp (u ^ 2 / 2) := funext standardGaussian_mgf
  rw [he]
  convert! (((hasDerivAt_id t).pow 2).div_const 2).exp using 1 <;> norm_num

theorem standardGaussian_mean_zero : (∫ z : ℝ, z ∂gaussianReal 0 1) = 0 := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
    rw [standardGaussian_integrableExpSet, interior_univ]
    exact Set.mem_univ _
  have h := deriv_mgf_zero h0
  rw [(standardGaussian_mgf_hasDerivAt 0).deriv] at h
  simpa using h.symm

theorem standardGaussian_second_moment : (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
    rw [standardGaussian_integrableExpSet, interior_univ]
    exact Set.mem_univ _
  have he : iteratedDeriv 1 (mgf id (gaussianReal 0 1)) = fun t => Real.exp (t ^ 2 / 2) * t := by
    funext t
    rw [iteratedDeriv_one]
    exact (standardGaussian_mgf_hasDerivAt t).deriv
  have hd := hasDerivAt_iteratedDeriv_mgf h0 1
  rw [he] at hd
  have hlast : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2) * t) 1 0 := by
    convert! ((((hasDerivAt_id (0 : ℝ)).pow 2).div_const 2).exp).mul (hasDerivAt_id 0) using 1 <;> norm_num
  simpa using hd.unique hlast

end
end Nonsmooth
