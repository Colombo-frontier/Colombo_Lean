import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic

/-!
Direct Gaussian integrals used by `lem:mixed-exp`. Scalar moment derivations
adapt the checked local GaussianRealMoments/GaussianFourth proof pattern,
with only Mathlib imports and the actual measure `gaussianReal 0 1`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Function
open scoped Topology
namespace HeavyTail.GaussianEstimates

theorem standard_mgf (t : ℝ) :
    mgf id (gaussianReal 0 1) t = Real.exp (t ^ 2 / 2) := by
  simpa only [zero_mul, NNReal.coe_one, one_mul, zero_add] using
    mgf_gaussianReal (X := id) (p := gaussianReal 0 1) (μ := 0) (v := 1) Measure.map_id t

theorem standard_exp_integrable (t : ℝ) :
    Integrable (fun z : ℝ => Real.exp (t * z)) (gaussianReal 0 1) := by
  by_contra hn
  have hz := integral_undef hn
  change mgf id (gaussianReal 0 1) t = 0 at hz
  rw [standard_mgf] at hz
  exact (Real.exp_ne_zero _) hz

theorem standard_integrableExpSet : integrableExpSet id (gaussianReal 0 1) = Set.univ := by
  exact Set.eq_univ_of_forall standard_exp_integrable

theorem standard_exp_interior (t : ℝ) :
    t ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
  rw [standard_integrableExpSet, interior_univ]
  trivial

theorem standard_power_integrable (n : ℕ) :
    Integrable (fun z : ℝ => z ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (standard_exp_interior 0) n

theorem standard_power_exp_integrable (n : ℕ) (t : ℝ) :
    Integrable (fun z : ℝ => z ^ n * Real.exp (t * z)) (gaussianReal 0 1) :=
  integrable_pow_mul_exp_of_mem_interior_integrableExpSet (standard_exp_interior t) n

theorem standard_mgf_derivative (t : ℝ) :
    HasDerivAt (mgf id (gaussianReal 0 1)) (Real.exp (t ^ 2 / 2) * t) t := by
  rw [show mgf id (gaussianReal 0 1) = fun u => Real.exp (u ^ 2 / 2) from funext standard_mgf]
  convert (((hasDerivAt_id t).pow 2).div_const 2).exp using 1 <;> simp only [id_eq] <;> ring

theorem standard_mean_zero : (∫ z : ℝ, z ∂gaussianReal 0 1) = 0 := by
  have h := deriv_mgf_zero (standard_exp_interior 0)
  rw [(standard_mgf_derivative 0).deriv] at h
  simpa using h.symm

theorem standard_weighted_second (t : ℝ) :
    (∫ z : ℝ, z ^ 2 * Real.exp (t * z) ∂gaussianReal 0 1) =
      Real.exp (t ^ 2 / 2) * (1 + t ^ 2) := by
  have he : iteratedDeriv 1 (mgf id (gaussianReal 0 1)) = fun u => Real.exp (u ^ 2 / 2) * u := by
    funext u
    rw [iteratedDeriv_one]
    exact (standard_mgf_derivative u).deriv
  have hd := hasDerivAt_iteratedDeriv_mgf (standard_exp_interior t) 1
  rw [he] at hd
  have hlast : HasDerivAt (fun u : ℝ => Real.exp (u ^ 2 / 2) * u)
      (Real.exp (t ^ 2 / 2) * (1 + t ^ 2)) t := by
    convert ((((hasDerivAt_id t).pow 2).div_const 2).exp).mul (hasDerivAt_id t)
      using 1 <;> simp only [id_eq] <;> ring
  simpa only [id_eq] using hd.unique hlast

theorem standard_second_moment : (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1) = 1 := by
  simpa using standard_weighted_second 0

theorem standard_fourth_moment : (∫ z : ℝ, z ^ 4 ∂gaussianReal 0 1) = 3 := by
  let g : ℝ → ℝ := fun t => Real.exp (t ^ 2 / 2)
  have he0 : mgf id (gaussianReal 0 1) = g := funext standard_mgf
  have h0 (t : ℝ) : HasDerivAt g (g t * t) t := by
    have h := standard_mgf_derivative t
    rw [he0] at h
    exact h
  have h1 (t : ℝ) : HasDerivAt (fun u => g u * u) (g t * (1 + t ^ 2)) t := by
    convert (h0 t).mul (hasDerivAt_id t) using 1 <;> simp only [id_eq] <;> ring
  have h2 (t : ℝ) : HasDerivAt (fun u => g u * (1 + u ^ 2)) (g t * (3 * t + t ^ 3)) t := by
    convert (h0 t).mul ((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)) using 1 <;>
      simp only [id_eq] <;> ring
  have h3 (t : ℝ) : HasDerivAt (fun u => g u * (3 * u + u ^ 3))
      (g t * (3 + 6 * t ^ 2 + t ^ 4)) t := by
    convert (h0 t).mul (((hasDerivAt_id t).const_mul 3).add ((hasDerivAt_id t).pow 3)) using 1 <;>
      simp only [id_eq] <;> ring
  have he1 : iteratedDeriv 1 (mgf id (gaussianReal 0 1)) = fun t => g t * t := by
    rw [iteratedDeriv_one, he0]
    exact funext (fun t => (h0 t).deriv)
  have he2 : iteratedDeriv 2 (mgf id (gaussianReal 0 1)) = fun t => g t * (1 + t ^ 2) := by
    rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, he1]
    exact funext (fun t => (h1 t).deriv)
  have he3 : iteratedDeriv 3 (mgf id (gaussianReal 0 1)) = fun t => g t * (3 * t + t ^ 3) := by
    rw [show 3 = 2 + 1 from rfl, iteratedDeriv_succ, he2]
    exact funext (fun t => (h2 t).deriv)
  have hm := hasDerivAt_iteratedDeriv_mgf (standard_exp_interior 0) 3
  rw [he3] at hm
  simpa [g] using hm.unique (h3 0)

theorem exp_mul_abs_le_two_exps (c x : ℝ) :
    Real.exp (c * |x|) ≤ Real.exp (c * x) + Real.exp (-c * x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg (lt_of_not_ge hx)]
    have he : c * -x = -c * x := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

theorem standard_exp_abs_integrable (c : ℝ) :
    Integrable (fun z : ℝ => Real.exp (c * |z|)) (gaussianReal 0 1) := by
  apply ((standard_exp_integrable c).add (standard_exp_integrable (-c))).mono'
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_mul_abs_le_two_exps c z

theorem standard_exp_abs_bound (c : ℝ) :
    (∫ z : ℝ, Real.exp (c * |z|) ∂gaussianReal 0 1) ≤ 2 * Real.exp (c ^ 2 / 2) := by
  have h := integral_mono (standard_exp_abs_integrable c)
    ((standard_exp_integrable c).add (standard_exp_integrable (-c)))
    (exp_mul_abs_le_two_exps c)
  simp only [Pi.add_apply] at h
  rw [integral_add (standard_exp_integrable c) (standard_exp_integrable (-c))] at h
  change _ ≤ mgf id (gaussianReal 0 1) c + mgf id (gaussianReal 0 1) (-c) at h
  rw [standard_mgf, standard_mgf, neg_sq] at h
  linarith

theorem standard_square_exp_abs_integrable (c : ℝ) :
    Integrable (fun z : ℝ => z ^ 2 * Real.exp (c * |z|)) (gaussianReal 0 1) := by
  apply ((standard_power_exp_integrable 2 c).add (standard_power_exp_integrable 2 (-c))).mono'
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      have h := mul_le_mul_of_nonneg_left (exp_mul_abs_le_two_exps c z) (sq_nonneg z)
      simpa only [mul_add] using h

theorem standard_square_exp_abs_bound (c : ℝ) :
    (∫ z : ℝ, z ^ 2 * Real.exp (c * |z|) ∂gaussianReal 0 1) ≤
      2 * Real.exp (c ^ 2 / 2) * (1 + c ^ 2) := by
  have hp (z : ℝ) : z ^ 2 * Real.exp (c * |z|) ≤
      z ^ 2 * Real.exp (c * z) + z ^ 2 * Real.exp (-c * z) := by
    simpa only [mul_add] using
      mul_le_mul_of_nonneg_left (exp_mul_abs_le_two_exps c z) (sq_nonneg z)
  have h := integral_mono (standard_square_exp_abs_integrable c)
    ((standard_power_exp_integrable 2 c).add (standard_power_exp_integrable 2 (-c))) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (standard_power_exp_integrable 2 c) (standard_power_exp_integrable 2 (-c)),
    standard_weighted_second, standard_weighted_second, neg_sq] at h
  nlinarith

theorem standard_exp_abs_uniform {c : ℝ} (hc : |c| ≤ 1) :
    (∫ z : ℝ, Real.exp (c * |z|) ∂gaussianReal 0 1) ≤ 2 * Real.exp (1 / 2) := by
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_abs c, abs_nonneg c]
  exact (standard_exp_abs_bound c).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))

theorem standard_square_exp_abs_uniform {c : ℝ} (hc : |c| ≤ 1) :
    (∫ z : ℝ, z ^ 2 * Real.exp (c * |z|) ∂gaussianReal 0 1) ≤ 4 * Real.exp (1 / 2) := by
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_abs c, abs_nonneg c]
  have he : Real.exp (c ^ 2 / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  have hp := mul_le_mul he (by linarith : 1 + c ^ 2 ≤ 2)
    (by positivity : 0 ≤ 1 + c ^ 2) (Real.exp_pos (1 / 2)).le
  have h := standard_square_exp_abs_bound c
  nlinarith

end HeavyTail.GaussianEstimates
