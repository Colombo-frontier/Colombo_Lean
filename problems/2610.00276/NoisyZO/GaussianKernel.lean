import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import NoisyZO.GaussianKL

/-!
# Gaussian observation kernels

This module packages a measurable, history-dependent mean as a unit-variance
Gaussian Markov kernel.  It connects the scalar Gaussian KL calculation to the
composition-product chain rule used for adaptive transcripts.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace NoisyZO

variable {α : Type*} [MeasurableSpace α]

/-- Unit-variance Gaussian observation kernel with a measurable mean. -/
noncomputable def gaussianOracleKernel (mean : α → ℝ) (hmean : Measurable mean) : Kernel α ℝ where
  toFun a := gaussianReal (mean a) 1
  measurable' := measurable_gaussianReal.comp (hmean.prodMk measurable_const)

@[simp]
lemma gaussianOracleKernel_apply (mean : α → ℝ) (hmean : Measurable mean) (a : α) :
    gaussianOracleKernel mean hmean a = gaussianReal (mean a) 1 := rfl

instance gaussianOracleKernel.instIsMarkovKernel (mean : α → ℝ) (hmean : Measurable mean) :
    IsMarkovKernel (gaussianOracleKernel mean hmean) where
  isProbabilityMeasure a := by
    change IsProbabilityMeasure (gaussianReal (mean a) 1)
    infer_instance

/-- The exact conditional KL cost at a fixed history. -/
theorem gaussianOracleKernel_kl_toReal
    (mean₁ mean₂ : α → ℝ) (hmean₁ : Measurable mean₁) (hmean₂ : Measurable mean₂)
    (a : α) :
    (InformationTheory.klDiv
      (gaussianOracleKernel mean₁ hmean₁ a)
      (gaussianOracleKernel mean₂ hmean₂ a)).toReal =
        (mean₁ a - mean₂ a) ^ 2 / 2 := by
  simp only [gaussianOracleKernel_apply, klDiv_gaussianReal_one_toReal]

/-- The exact ENNReal-valued conditional KL cost at a fixed history. -/
theorem gaussianOracleKernel_kl
    (mean₁ mean₂ : α → ℝ) (hmean₁ : Measurable mean₁) (hmean₂ : Measurable mean₂)
    (a : α) :
    InformationTheory.klDiv
      (gaussianOracleKernel mean₁ hmean₁ a)
      (gaussianOracleKernel mean₂ hmean₂ a) =
        ENNReal.ofReal ((mean₁ a - mean₂ a) ^ 2 / 2) := by
  simp only [gaussianOracleKernel_apply, klDiv_gaussianReal_one]

/-- Conditional Gaussian KL integrated over a common history law. -/
theorem klDiv_gaussianOracle_compProd_sameBase
    (μ : Measure α) [IsFiniteMeasure μ]
    (mean₁ mean₂ : α → ℝ) (hmean₁ : Measurable mean₁) (hmean₂ : Measurable mean₂) :
    InformationTheory.klDiv
        (μ ⊗ₘ gaussianOracleKernel mean₁ hmean₁)
        (μ ⊗ₘ gaussianOracleKernel mean₂ hmean₂) =
      ∫⁻ a, ENNReal.ofReal ((mean₁ a - mean₂ a) ^ 2 / 2) ∂μ := by
  let κ₁ : Kernel α ℝ := gaussianOracleKernel mean₁ hmean₁
  let κ₂ : Kernel α ℝ := gaussianOracleKernel mean₂ hmean₂
  have hpoint : ∀ a, κ₁ a ≪ κ₂ a := by
    intro a
    change gaussianReal (mean₁ a) 1 ≪ gaussianReal (mean₂ a) 1
    exact (gaussianReal_absolutelyContinuous (mean₁ a) (v := (1 : ℝ≥0)) (by norm_num)).trans
      (gaussianReal_absolutelyContinuous' (mean₂ a) (v := (1 : ℝ≥0)) (by norm_num))
  have hac : μ ⊗ₘ κ₁ ≪ μ ⊗ₘ κ₂ := by
    rw [Measure.absolutelyContinuous_compProd_right_iff]
    exact ae_of_all μ hpoint
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac]
  calc
    ∫⁻ p, ENNReal.ofReal
        (InformationTheory.klFun (((μ ⊗ₘ κ₁).rnDeriv (μ ⊗ₘ κ₂) p).toReal))
        ∂(μ ⊗ₘ κ₂) =
        ∫⁻ p, ENNReal.ofReal
          (InformationTheory.klFun ((κ₁.rnDeriv κ₂ p.1 p.2).toReal))
          ∂(μ ⊗ₘ κ₂) := by
            apply lintegral_congr_ae
            filter_upwards [rnDeriv_measure_compProd_right μ κ₁ κ₂] with p hp
            rw [hp]
    _ = ∫⁻ a, ∫⁻ y, ENNReal.ofReal
          (InformationTheory.klFun ((κ₁.rnDeriv κ₂ a y).toReal)) ∂κ₂ a ∂μ := by
            rw [Measure.lintegral_compProd (by fun_prop)]
    _ = ∫⁻ a, InformationTheory.klDiv (κ₁ a) (κ₂ a) ∂μ := by
            apply lintegral_congr
            intro a
            rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (hpoint a)]
            apply lintegral_congr_ae
            filter_upwards [κ₁.rnDeriv_eq_rnDeriv_measure] with y hy
            rw [hy]
    _ = ∫⁻ a, ENNReal.ofReal ((mean₁ a - mean₂ a) ^ 2 / 2) ∂μ := by
            apply lintegral_congr
            intro a
            exact gaussianOracleKernel_kl mean₁ mean₂ hmean₁ hmean₂ a

/-- Real-valued conditional Gaussian KL identity when the squared signal is integrable. -/
theorem klDiv_gaussianOracle_compProd_sameBase_toReal
    (μ : Measure α) [IsFiniteMeasure μ]
    (mean₁ mean₂ : α → ℝ) (hmean₁ : Measurable mean₁) (hmean₂ : Measurable mean₂)
    (hint : Integrable (fun a ↦ (mean₁ a - mean₂ a) ^ 2 / 2) μ) :
    (InformationTheory.klDiv
        (μ ⊗ₘ gaussianOracleKernel mean₁ hmean₁)
        (μ ⊗ₘ gaussianOracleKernel mean₂ hmean₂)).toReal =
      ∫ a, (mean₁ a - mean₂ a) ^ 2 / 2 ∂μ := by
  rw [klDiv_gaussianOracle_compProd_sameBase]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all μ fun a ↦ div_nonneg (sq_nonneg _) (by norm_num))]
  rw [ENNReal.toReal_ofReal]
  exact integral_nonneg fun a ↦ div_nonneg (sq_nonneg _) (by norm_num)

/-- One adaptive observation adds a composition-product KL term. -/
theorem gaussianOracle_compProd_chainRule
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (mean₁ mean₂ : α → ℝ) (hmean₁ : Measurable mean₁) (hmean₂ : Measurable mean₂) :
    InformationTheory.klDiv
        (μ ⊗ₘ gaussianOracleKernel mean₁ hmean₁)
        (ν ⊗ₘ gaussianOracleKernel mean₂ hmean₂) =
      InformationTheory.klDiv μ ν +
        InformationTheory.klDiv
          (μ ⊗ₘ gaussianOracleKernel mean₁ hmean₁)
          (μ ⊗ₘ gaussianOracleKernel mean₂ hmean₂) := by
  exact InformationTheory.klDiv_compProd_eq_add _ _ _ _

/-- Real-valued one-step adaptive Gaussian chain rule. -/
theorem gaussianOracle_compProd_chainRule_toReal
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (mean₁ mean₂ : α → ℝ) (hmean₁ : Measurable mean₁) (hmean₂ : Measurable mean₂)
    (hfinite : InformationTheory.klDiv μ ν ≠ ∞)
    (hint : Integrable (fun a ↦ (mean₁ a - mean₂ a) ^ 2 / 2) μ) :
    (InformationTheory.klDiv
        (μ ⊗ₘ gaussianOracleKernel mean₁ hmean₁)
        (ν ⊗ₘ gaussianOracleKernel mean₂ hmean₂)).toReal =
      (InformationTheory.klDiv μ ν).toReal +
        ∫ a, (mean₁ a - mean₂ a) ^ 2 / 2 ∂μ := by
  let κ₁ : Kernel α ℝ := gaussianOracleKernel mean₁ hmean₁
  let κ₂ : Kernel α ℝ := gaussianOracleKernel mean₂ hmean₂
  have hcond : InformationTheory.klDiv (μ ⊗ₘ κ₁) (μ ⊗ₘ κ₂) ≠ ∞ := by
    rw [klDiv_gaussianOracle_compProd_sameBase]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all μ fun a ↦ div_nonneg (sq_nonneg _) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  rw [gaussianOracle_compProd_chainRule, ENNReal.toReal_add hfinite hcond]
  congr 1
  exact klDiv_gaussianOracle_compProd_sameBase_toReal μ mean₁ mean₂ hmean₁ hmean₂ hint

end NoisyZO
