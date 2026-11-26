import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic

/-! # Moments of the genuine Gaussian law

The mean and second moment are derived from Mathlib's Gaussian measure and its
moment generating function. No moment or distribution certificate is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Bilevel.GaussianMoments

theorem mgf_eq (m : ℝ) (v : ℝ≥0) :
    mgf id (gaussianReal m v) = fun t => Real.exp (m * t + (v : ℝ) * t ^ 2 / 2) := by
  funext t
  exact mgf_gaussianReal (by simp) t

theorem integrable_exp (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gaussianReal m v) := by
  by_contra h
  have hz : mgf id (gaussianReal m v) t = 0 := integral_undef h
  rw [mgf_eq] at hz
  exact (Real.exp_pos _).ne' hz

theorem exp_set (m : ℝ) (v : ℝ≥0) :
    integrableExpSet id (gaussianReal m v) = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact integrable_exp m v t

theorem interior_exp_set (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    t ∈ interior (integrableExpSet id (gaussianReal m v)) := by
  simp [exp_set]

theorem mgf_derivative (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    HasDerivAt (mgf id (gaussianReal m v))
      ((m + (v : ℝ) * t) * Real.exp (m * t + (v : ℝ) * t ^ 2 / 2)) t := by
  rw [mgf_eq]
  convert ((((hasDerivAt_id t).const_mul m).add
    (((hasDerivAt_id t).pow 2).const_mul (v : ℝ) |>.div_const 2)).exp) using 1
  simp only [id_eq]
  ring

theorem mean (m : ℝ) (v : ℝ≥0) : (∫ x : ℝ, x ∂gaussianReal m v) = m := by
  have h := (mgf_derivative m v 0).unique (hasDerivAt_mgf (interior_exp_set m v 0))
  simpa using h.symm

theorem second_moment (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal m v) = m ^ 2 + (v : ℝ) := by
  have hd : deriv (mgf id (gaussianReal m v)) =
      fun t => (m + (v : ℝ) * t) * Real.exp (m * t + (v : ℝ) * t ^ 2 / 2) := by
    funext t
    exact (mgf_derivative m v t).deriv
  have h0 := hasDerivAt_iteratedDeriv_mgf (interior_exp_set m v 0) 1
  simp only [iteratedDeriv_one, hd] at h0
  have h1 := (((hasDerivAt_id (0 : ℝ)).const_mul (v : ℝ)).const_add m).mul
    ((((hasDerivAt_id (0 : ℝ)).const_mul m).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (v : ℝ) |>.div_const 2)).exp)
  have h := h0.unique h1
  simpa [pow_two, add_comm] using h

theorem integrable_pow (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal m v) := by
  simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (interior_exp_set m v 0) n

theorem integrable_id (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x) (gaussianReal m v) := by
  simpa using integrable_pow m v 1

theorem centered_second_moment (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, (x - m) ^ 2 ∂gaussianReal m v) = (v : ℝ) := by
  have hf : (fun x : ℝ => (x - m) ^ 2) = fun x => x ^ 2 - 2 * m * x + m ^ 2 := by
    funext x
    ring
  have hi : Integrable (fun x : ℝ => x ^ 2 - 2 * m * x) (gaussianReal m v) :=
    (integrable_pow m v 2).sub ((integrable_id m v).const_mul (2 * m))
  rw [hf, integral_add hi (integrable_const (m ^ 2)),
    integral_sub (integrable_pow m v 2) ((integrable_id m v).const_mul (2 * m)),
    integral_const_mul, second_moment, mean]
  simp
  ring

end Bilevel.GaussianMoments
