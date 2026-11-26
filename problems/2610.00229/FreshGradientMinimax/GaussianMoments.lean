import FreshGradientMinimax.Basic
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.Moments.MGFAnalytic

/-! Gaussian integrability, means and second moments, derived from the
library's Gaussian moment generating function. Degenerate variance is included. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem gaussianReal_mgf (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    mgf id (gaussianReal m v) t = Real.exp (m * t + (v : ℝ) * t ^ 2 / 2) :=
  mgf_gaussianReal (Measure.map_id) t

theorem gaussianReal_exp_integrable (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gaussianReal m v) := by
  by_contra h
  have hz := mgf_undef (X := id) h
  rw [gaussianReal_mgf] at hz
  exact Real.exp_ne_zero _ hz

theorem gaussianReal_exp_interior (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    t ∈ interior (integrableExpSet id (gaussianReal m v)) := by
  have he : integrableExpSet id (gaussianReal m v) = Set.univ := by
    ext u
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact gaussianReal_exp_integrable m v u
  rw [he, interior_univ]
  trivial

theorem gaussianReal_pow_integrable (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal m v) :=
  integrable_pow_of_mem_interior_integrableExpSet (gaussianReal_exp_interior m v 0) n

theorem gaussianReal_id_integrable (m : ℝ) (v : ℝ≥0) :
    Integrable id (gaussianReal m v) := by
  simpa only [pow_one] using gaussianReal_pow_integrable m v 1

theorem gaussian_exp_derivative (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (m * u + (v : ℝ) * u ^ 2 / 2))
      ((m + (v : ℝ) * t) * Real.exp (m * t + (v : ℝ) * t ^ 2 / 2)) t := by
  apply (((hasDerivAt_id t).const_mul m).add
    ((((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2)).exp.congr_deriv
  simp only [id_eq, mul_one, pow_one, Nat.cast_ofNat]
  ring

theorem gaussianReal_weighted_mean (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    (∫ x : ℝ, x * Real.exp (t * x) ∂gaussianReal m v) =
      (m + (v : ℝ) * t) * Real.exp (m * t + (v : ℝ) * t ^ 2 / 2) := by
  have h := hasDerivAt_mgf (gaussianReal_exp_interior m v t)
  have he : mgf id (gaussianReal m v) =
      (fun u : ℝ => Real.exp (m * u + (v : ℝ) * u ^ 2 / 2)) := funext (gaussianReal_mgf m v)
  rw [he] at h
  exact h.unique (gaussian_exp_derivative m v t)

theorem gaussianReal_mean (m : ℝ) (v : ℝ≥0) : (∫ x : ℝ, x ∂gaussianReal m v) = m := by
  simpa using gaussianReal_weighted_mean m v 0

theorem gaussianReal_second_moment (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal m v) = (v : ℝ) + m ^ 2 := by
  have h := hasDerivAt_integral_pow_mul_exp_real (gaussianReal_exp_interior m v 0) 1
  have he : (fun t : ℝ => ∫ x : ℝ, x ^ 1 * Real.exp (t * x) ∂gaussianReal m v) =
      (fun t : ℝ => (m + (v : ℝ) * t) * Real.exp (m * t + (v : ℝ) * t ^ 2 / 2)) := by
    funext t
    simpa only [pow_one] using gaussianReal_weighted_mean m v t
  change HasDerivAt (fun t : ℝ => ∫ x : ℝ, x ^ 1 * Real.exp (t * x) ∂gaussianReal m v)
    (∫ x : ℝ, x ^ (1 + 1) * Real.exp (0 * x) ∂gaussianReal m v) 0 at h
  rw [he] at h
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul (v : ℝ)).const_add m).mul
    (gaussian_exp_derivative m v 0)
  have hu := h.unique hd
  simpa [pow_two] using hu

theorem gaussianReal_centered_square_integrable (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => (x - m) ^ 2) (gaussianReal m v) := by
  have h := ((gaussianReal_pow_integrable m v 2).sub
    ((gaussianReal_id_integrable m v).const_mul (2 * m))).add (integrable_const (m ^ 2))
  convert h using 1
  funext x
  dsimp only [id_eq, Pi.add_apply, Pi.sub_apply]
  ring

theorem gaussianReal_variance (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, (x - m) ^ 2 ∂gaussianReal m v) = (v : ℝ) := by
  have he (x : ℝ) : (x - m) ^ 2 = x ^ 2 - 2 * m * x + m ^ 2 := by ring
  simp_rw [he]
  rw [integral_add (f := fun x : ℝ => x ^ 2 - 2 * m * x) (g := fun _ : ℝ => m ^ 2)
      ((gaussianReal_pow_integrable m v 2).sub
      ((gaussianReal_id_integrable m v).const_mul (2 * m))) (integrable_const _),
    integral_sub (f := fun x : ℝ => x ^ 2) (g := fun x : ℝ => 2 * m * x)
      (gaussianReal_pow_integrable m v 2) ((gaussianReal_id_integrable m v).const_mul (2 * m)),
    integral_const_mul, gaussianReal_second_moment, gaussianReal_mean]
  simp
  ring

end FreshGradientMinimax
