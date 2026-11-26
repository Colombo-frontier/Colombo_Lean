import GradientHessian.GaussianConcentrationIntegrability
import LowRank.GaussianRadialIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! The exact expectation bounds for the standard Gaussian norm.  A radial
integral and Gamma log-convexity prove this consequence independently of the
still separate general Gaussian functional inequalities. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianHilbert
open scoped Matrix

theorem gamma_midpoint_square_le {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Real.Gamma ((s + t) / 2) ^ 2 ≤ Real.Gamma s * Real.Gamma t := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hs ht
    (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have he : (1 / 2 : ℝ) * s + 1 / 2 * t = (s + t) / 2 := by ring
  rw [he, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have h2 := (sq_le_sq₀ (Real.Gamma_pos_of_pos (by linarith : 0 < (s + t) / 2)).le
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr h
  simpa only [mul_pow, Real.sq_sqrt (Real.Gamma_pos_of_pos hs).le,
    Real.sq_sqrt (Real.Gamma_pos_of_pos ht).le] using h2

theorem gamma_half_ratio_upper {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 1 / 2) ^ 2 ≤ x * Real.Gamma x ^ 2 := by
  have h := gamma_midpoint_square_le hx (show 0 < x + 1 by linarith)
  have he : (x + (x + 1)) / 2 = x + 1 / 2 := by ring
  rw [he, Real.Gamma_add_one hx.ne'] at h
  nlinarith only [h]

theorem gamma_half_ratio_lower {x : ℝ} (hx : 1 / 2 < x) :
    (x - 1 / 2) * Real.Gamma x ^ 2 ≤ Real.Gamma (x + 1 / 2) ^ 2 := by
  have hx' : 0 < x - 1 / 2 := by linarith
  have h := gamma_midpoint_square_le hx' (show 0 < x + 1 / 2 by linarith)
  have he : (x - 1 / 2 + (x + 1 / 2)) / 2 = x := by ring
  rw [he] at h
  have hg : Real.Gamma (x + 1 / 2) = (x - 1 / 2) * Real.Gamma (x - 1 / 2) := by
    convert Real.Gamma_add_one hx'.ne' using 1
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_left h hx'.le
  calc
    (x - 1 / 2) * Real.Gamma x ^ 2 ≤
      (x - 1 / 2) * (Real.Gamma (x - 1 / 2) * Real.Gamma (x + 1 / 2)) := hm
    _ = Real.Gamma (x + 1 / 2) ^ 2 := by rw [← mul_assoc, ← hg, pow_two]

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem mean_norm_formula :
    (∫ x : E, ‖x‖ ∂euclideanGaussianLaw E) =
      Real.sqrt 2 * Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1 / 2) /
        Real.Gamma ((Module.finrank ℝ E : ℝ) / 2) := by
  rw [euclideanGaussianLaw,
    integral_map_of_stronglyMeasurable (gaussianSynthesis_continuous E).measurable
      continuous_norm.stronglyMeasurable]
  have he (v : Fin (Module.finrank ℝ E) → ℝ) :
      ‖gaussianSynthesis E v‖ = (v ⬝ᵥ v) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_sq (norm_nonneg (gaussianSynthesis E v)),
      gaussianSynthesis_norm_square, Real.sqrt_eq_rpow]
    congr 1
    simp only [GaussianSquare.energy, dotProduct, pow_two]
  simp_rw [he]
  change (∫ v : Fin (Module.finrank ℝ E) → ℝ, (v ⬝ᵥ v) ^ (1 / 2 : ℝ)
    ∂LowRank.iidVectorLaw (Module.finrank ℝ E) 1) = _
  rw [LowRank.gaussian_radial_integral Module.finrank_pos (by positivity), ← Real.sqrt_eq_rpow]

theorem mean_norm_bounds :
    Real.sqrt ((Module.finrank ℝ E : ℝ) - 1) ≤
        (∫ x : E, ‖x‖ ∂euclideanGaussianLaw E) ∧
      (∫ x : E, ‖x‖ ∂euclideanGaussianLaw E) ≤ Real.sqrt (Module.finrank ℝ E) := by
  let x : ℝ := (Module.finrank ℝ E : ℝ) / 2
  have hx : 0 < x := by dsimp [x]; exact div_pos (by exact_mod_cast Module.finrank_pos) (by norm_num)
  have hg : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hmean : 0 ≤ ∫ z : E, ‖z‖ ∂euclideanGaussianLaw E := integral_nonneg (fun z => norm_nonneg z)
  have hformula := mean_norm_formula E
  change (∫ z : E, ‖z‖ ∂euclideanGaussianLaw E) =
    Real.sqrt 2 * Real.Gamma (x + 1 / 2) / Real.Gamma x at hformula
  have hmul := (eq_div_iff hg.ne').mp hformula
  have hsq : (∫ z : E, ‖z‖ ∂euclideanGaussianLaw E) ^ 2 * Real.Gamma x ^ 2 =
      2 * Real.Gamma (x + 1 / 2) ^ 2 := by
    have h := congrArg (fun y : ℝ => y ^ 2) hmul
    simpa only [mul_pow, hsqrt] using h
  have hx_dim : 2 * x = (Module.finrank ℝ E : ℝ) := by dsimp [x]; ring
  constructor
  · by_cases hm : Module.finrank ℝ E = 1
    · simpa only [hm, Nat.cast_one, sub_self, Real.sqrt_zero] using hmean
    have hm1 : 1 < Module.finrank ℝ E := by have := Module.finrank_pos (R := ℝ) (M := E); omega
    have hxhalf : 1 / 2 < x := by
      have hr : (1 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hm1
      dsimp [x]
      linarith
    have hl := gamma_half_ratio_lower hxhalf
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hmean).mp
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) - 1 by
      have hr : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hm1.le
      linarith)]
    have hgsq : 0 < Real.Gamma x ^ 2 := sq_pos_of_pos hg
    apply (mul_le_mul_right hgsq).mp
    rw [hsq, ← hx_dim]
    nlinarith only [hl]
  · have hu := gamma_half_ratio_upper hx
    apply (sq_le_sq₀ hmean (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    have hgsq : 0 < Real.Gamma x ^ 2 := sq_pos_of_pos hg
    apply (mul_le_mul_right hgsq).mp
    rw [hsq, ← hx_dim]
    nlinarith only [hu]

end GradientHessian.GaussianConcentration
