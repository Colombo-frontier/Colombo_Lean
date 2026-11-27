import Nonsmooth.IntervalDensityLaw
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem strong_potential_quadratic_lower (U s : ℝ → ℝ) (hs : Continuous s) {ρ : ℝ}
    (hd : ∀ x, HasDerivAt U (s x) x) (hmono : Monotone (fun x => s x - ρ * x)) (x : ℝ) :
    U 0 + s 0 * x + ρ / 2 * x ^ 2 ≤ U x := by
  have hU (a b : ℝ) : (∫ t in a..b, s t) = U b - U a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hs.intervalIntegrable a b)
  have hlin : Continuous (fun t : ℝ => s 0 + ρ * t) := by fun_prop
  have hI (a b : ℝ) : (∫ t in a..b, s 0 + ρ * t) =
      (s 0 * b + ρ / 2 * b ^ 2) - (s 0 * a + ρ / 2 * a ^ 2) := by
    have hder (t : ℝ) : HasDerivAt (fun z : ℝ => s 0 * z + ρ / 2 * z ^ 2) (s 0 + ρ * t) t := by
      convert! ((hasDerivAt_id t).const_mul (s 0)).add
        (((hasDerivAt_id t).pow 2).const_mul (ρ / 2)) using 1 <;>
        (try simp only [id_eq]) <;> ring
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) (hlin.intervalIntegrable a b)
  rcases le_total 0 x with hx | hx
  · have he : (∫ t in (0 : ℝ)..x, s 0 + ρ * t) ≤ ∫ t in (0 : ℝ)..x, s t := by
      apply intervalIntegral.integral_mono_on hx (hlin.intervalIntegrable 0 x) (hs.intervalIntegrable 0 x)
      intro t ht
      have h := hmono ht.1
      try dsimp only at h
      nlinarith
    rw [hI, hU] at he
    nlinarith
  · have he : (∫ t in x..0, s t) ≤ ∫ t in x..0, s 0 + ρ * t := by
      apply intervalIntegral.integral_mono_on hx (hs.intervalIntegrable x 0) (hlin.intervalIntegrable x 0)
      intro t ht
      have h := hmono ht.2
      try dsimp only at h
      nlinarith
    rw [hU, hI] at he
    nlinarith

/-- A strongly convex potential has an explicit Gaussian envelope, without assuming
normalization or moment bounds in advance. -/
theorem strong_potential_gaussian_envelope (U s : ℝ → ℝ) (hs : Continuous s) {ρ : ℝ} (hρ : 0 < ρ)
    (hd : ∀ x, HasDerivAt U (s x) x) (hmono : Monotone (fun x => s x - ρ * x)) (x : ℝ) :
    Real.exp (-U x) ≤ Real.exp ((s 0) ^ 2 / ρ - U 0) * Real.exp (-(ρ / 4) * x ^ 2) := by
  have hlow := strong_potential_quadratic_lower U s hs hd hmono x
  have he : ρ * ((s 0) ^ 2 / ρ) = (s 0) ^ 2 := by field_simp
  have hy : 0 ≤ ρ / 4 * x ^ 2 + s 0 * x + (s 0) ^ 2 / ρ := by
    apply nonneg_of_mul_nonneg_left (b := ρ) ?_ hρ
    nlinarith [sq_nonneg (ρ * x / 2 + s 0)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- All polynomial moments of exp(-U) are finite under a globally strongly increasing score. -/
theorem strong_potential_polynomial_integrable (U s : ℝ → ℝ) (hU : Continuous U)
    (hs : Continuous s) {ρ : ℝ} (hρ : 0 < ρ)
    (hd : ∀ x, HasDerivAt U (s x) x) (hmono : Monotone (fun x => s x - ρ * x)) (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m * Real.exp (-U x)) := by
  have hg : Integrable (fun x : ℝ => x ^ m * Real.exp (-(ρ / 4) * x ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < ρ / 4)
        (show (-1 : ℝ) < (m : ℝ) from lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg m)))
  have hc : Continuous (fun x : ℝ => x ^ m * Real.exp (-U x)) := by fun_prop
  apply (hg.norm.const_mul (Real.exp ((s 0) ^ 2 / ρ - U 0))).mono' hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  have ht := mul_le_mul_of_nonneg_left (strong_potential_gaussian_envelope U s hs hρ hd hmono x)
    (abs_nonneg (x ^ m))
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_left_comm, mul_assoc] using ht

end
end Nonsmooth
