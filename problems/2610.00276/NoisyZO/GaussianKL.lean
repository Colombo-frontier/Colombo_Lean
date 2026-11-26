import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Tilted

/-!
# Equal-variance Gaussian KL divergence

This file supplies the measure-theoretic one-step identity used by the adaptive
lower bound.  We first compute the reverse KL divergence from a Gaussian law to
its linear exponential tilt.  A later lemma identifies that tilt with the
corresponding shifted Gaussian law.
-/

open Real
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace NoisyZO

/-- The normalizing constant for a linear exponential tilt of a real Gaussian. -/
lemma gaussian_linear_tilt_normalizer (m t : ℝ) (v : ℝ≥0) :
    ∫ x, exp (t * x) ∂gaussianReal m v = exp (m * t + (v : ℝ) * t ^ 2 / 2) := by
  simpa only [mgf, id_eq] using
    congrFun (mgf_fun_id_gaussianReal (μ := m) (v := v)) t

/-- A real Gaussian has an integrable identity random variable. -/
lemma integrable_id_gaussianReal (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x) (gaussianReal m v) := by
  have h : Integrable id (gaussianReal m v) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal (μ := m) (v := v) 1)
  exact h.congr (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Reverse KL from a Gaussian to its linear exponential tilt. -/
theorem klDiv_gaussian_tilt_toReal (m t : ℝ) :
    (InformationTheory.klDiv
      (gaussianReal m 1)
      ((gaussianReal m 1).tilted (fun x : ℝ ↦ t * x))).toReal = t ^ 2 / 2 := by
  let μ : Measure ℝ := gaussianReal m 1
  let f : ℝ → ℝ := fun x ↦ t * x
  have hf : Integrable f μ := by
    exact (integrable_id_gaussianReal m 1).const_mul t
  have hexp : Integrable (fun x ↦ exp (f x)) μ := by
    simpa only [μ, f] using
      (integrable_exp_mul_gaussianReal (μ := m) (v := (1 : ℝ≥0)) t)
  have hac : μ ≪ μ.tilted f := absolutelyContinuous_tilted hexp
  have hmass : μ Set.univ = (μ.tilted f) Set.univ := by
    simp only [μ]
    let _ : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted hexp
    simp
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac hmass]
  have hself : Integrable (llr μ μ) μ := by
    exact (integrable_const (c := (0 : ℝ))).congr (llr_self μ).symm
  rw [integral_llr_tilted_right (μ := μ) (ν := μ) (f := f)
    (Measure.AbsolutelyContinuous.rfl) hf hexp hself]
  have hself_integral : ∫ x, llr μ μ x ∂μ = 0 := by
    rw [integral_congr_ae (llr_self μ)]
    simp
  rw [hself_integral]
  have hmean : ∫ x, f x ∂μ = t * m := by
    change ∫ x, t * x ∂gaussianReal m 1 = t * m
    rw [integral_const_mul]
    simp
  have hnorm : ∫ x, exp (f x) ∂μ = exp (m * t + t ^ 2 / 2) := by
    simpa only [μ, f, NNReal.coe_one, one_mul] using
      gaussian_linear_tilt_normalizer m t 1
  rw [hmean, hnorm, log_exp]
  ring

/-- The moment-generating function of a linearly tilted unit-variance Gaussian. -/
lemma mgf_id_gaussian_linear_tilt (m t : ℝ) :
    mgf id ((gaussianReal m 1).tilted (fun x : ℝ ↦ t * x)) =
      fun s ↦ exp ((m + t) * s + s ^ 2 / 2) := by
  funext s
  rw [mgf, integral_exp_tilted]
  have hnum :
      ∫ x, exp (((fun x : ℝ ↦ t * x) + fun x : ℝ ↦ s * id x) x)
        ∂gaussianReal m 1 =
        exp (m * (t + s) + (t + s) ^ 2 / 2) := by
    calc
      ∫ x, exp (((fun x : ℝ ↦ t * x) + fun x : ℝ ↦ s * id x) x)
          ∂gaussianReal m 1 =
          ∫ x, exp ((t + s) * x) ∂gaussianReal m 1 := by
            apply integral_congr_ae
            filter_upwards with x
            congr 1
            simp only [Pi.add_apply, id_eq]
            ring
      _ = exp (m * (t + s) + (t + s) ^ 2 / 2) := by
        simpa only [NNReal.coe_one, one_mul] using
          gaussian_linear_tilt_normalizer m (t + s) 1
  have hden :
      ∫ x, exp (t * x) ∂gaussianReal m 1 = exp (m * t + t ^ 2 / 2) := by
    simpa only [NNReal.coe_one, one_mul] using gaussian_linear_tilt_normalizer m t 1
  rw [hnum, hden, ← exp_sub]
  congr 1
  ring

/-- Linear exponential tilting shifts the mean of a unit-variance Gaussian. -/
theorem gaussianReal_tilt_linear (m t : ℝ) :
    (gaussianReal m 1).tilted (fun x : ℝ ↦ t * x) = gaussianReal (m + t) 1 := by
  let ν : Measure ℝ := (gaussianReal m 1).tilted (fun x : ℝ ↦ t * x)
  have hexp : Integrable (fun x : ℝ ↦ exp (t * x)) (gaussianReal m 1) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := m) (v := (1 : ℝ≥0)) t)
  let _ : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hexp
  have hmgf : mgf id (gaussianReal (m + t) 1) = mgf id ν := by
    rw [mgf_id_gaussianReal]
    simpa only [ν, NNReal.coe_one, one_mul] using
      (mgf_id_gaussian_linear_tilt m t).symm
  have hcomplex :
      complexMGF id (gaussianReal (m + t) 1) = complexMGF id ν := by
    funext z
    exact eqOn_complexMGF_of_mgf hmgf (by simp)
  exact (Measure.ext_of_complexMGF_id_eq hcomplex).symm

/-- The log-likelihood ratio of two unit-variance Gaussians is affine. -/
theorem llr_gaussianReal_one (m₁ m₂ : ℝ) :
    llr (gaussianReal m₁ 1) (gaussianReal m₂ 1) =ᵐ[gaussianReal m₁ 1]
      fun x ↦ (m₁ - m₂) * x + (m₂ ^ 2 - m₁ ^ 2) / 2 := by
  let μ : Measure ℝ := gaussianReal m₁ 1
  let t : ℝ := m₂ - m₁
  let f : ℝ → ℝ := fun x ↦ t * x
  have hexp : Integrable (fun x ↦ exp (f x)) μ := by
    simpa only [μ, f] using
      (integrable_exp_mul_gaussianReal (μ := m₁) (v := (1 : ℝ≥0)) t)
  have htilt : μ.tilted f = gaussianReal m₂ 1 := by
    dsimp only [μ, f, t]
    rw [gaussianReal_tilt_linear]
    congr 2
    ring
  have hllr := llr_tilted_right (μ := μ) (ν := μ) (f := f)
    (Measure.AbsolutelyContinuous.rfl) hexp
  have hnorm : ∫ x, exp (f x) ∂μ = exp (m₁ * t + t ^ 2 / 2) := by
    simpa only [μ, f, NNReal.coe_one, one_mul] using
      gaussian_linear_tilt_normalizer m₁ t 1
  rw [htilt] at hllr
  filter_upwards [hllr, llr_self μ] with x hx hself
  rw [hx, hself, hnorm, log_exp]
  simp only [f, t, Pi.zero_apply, add_zero]
  ring

/-- The Gaussian log-likelihood ratio is integrable under its first law. -/
theorem integrable_llr_gaussianReal_one (m₁ m₂ : ℝ) :
    Integrable (llr (gaussianReal m₁ 1) (gaussianReal m₂ 1))
      (gaussianReal m₁ 1) := by
  have haffine : Integrable
      (fun x ↦ (m₁ - m₂) * x + (m₂ ^ 2 - m₁ ^ 2) / 2)
      (gaussianReal m₁ 1) :=
    ((integrable_id_gaussianReal m₁ 1).const_mul (m₁ - m₂)).add
      (integrable_const (c := (m₂ ^ 2 - m₁ ^ 2) / 2))
  exact haffine.congr (llr_gaussianReal_one m₁ m₂).symm

/-- Closed form for KL divergence between unit-variance real Gaussians. -/
theorem klDiv_gaussianReal_one_toReal (m₁ m₂ : ℝ) :
    (InformationTheory.klDiv (gaussianReal m₁ 1) (gaussianReal m₂ 1)).toReal =
      (m₁ - m₂) ^ 2 / 2 := by
  have htilt := gaussianReal_tilt_linear m₁ (m₂ - m₁)
  have hshift : m₁ + (m₂ - m₁) = m₂ := by ring
  rw [hshift] at htilt
  rw [← htilt, klDiv_gaussian_tilt_toReal]
  ring

/-- ENNReal-valued closed form for KL divergence between unit-variance Gaussians. -/
theorem klDiv_gaussianReal_one (m₁ m₂ : ℝ) :
    InformationTheory.klDiv (gaussianReal m₁ 1) (gaussianReal m₂ 1) =
      ENNReal.ofReal ((m₁ - m₂) ^ 2 / 2) := by
  have hac : gaussianReal m₁ 1 ≪ gaussianReal m₂ 1 :=
    (gaussianReal_absolutelyContinuous m₁ (by norm_num)).trans
      (gaussianReal_absolutelyContinuous' m₂ (by norm_num))
  have hne : InformationTheory.klDiv (gaussianReal m₁ 1) (gaussianReal m₂ 1) ≠ ∞ :=
    InformationTheory.klDiv_ne_top hac (integrable_llr_gaussianReal_one m₁ m₂)
  rw [← ENNReal.ofReal_toReal hne, klDiv_gaussianReal_one_toReal]

end NoisyZO
