import SecondOrder.LikelihoodNormBound
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

namespace SecondOrder
noncomputable section
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountablyGenerated β]

/-- A jointly measurable version of the log-likelihood ratio of two kernels. -/
def kernelLogLikelihood (K Q : Kernel α β) (a : α) (b : β) : ℝ :=
  Real.log (K.rnDeriv Q a b).toReal

theorem kernelLogLikelihood_measurable (K Q : Kernel α β) :
    Measurable (Function.uncurry (kernelLogLikelihood K Q)) :=
  (K.measurable_rnDeriv Q).ennreal_toReal.log

variable {K Q : Kernel α β} [IsMarkovKernel K] [IsMarkovKernel Q]

theorem kernelLogLikelihood_eq_llr {a : α} (hac : K a ≪ Q a) :
    kernelLogLikelihood K Q a =ᵐ[K a] llr (K a) (Q a) := by
  filter_upwards [hac.ae_le (K.rnDeriv_eq_rnDeriv_measure (η := Q) (a := a))] with b hb
  simp only [kernelLogLikelihood,llr_def,hb]

theorem kernelLogLikelihood_integrable {a : α} (hfin : klDiv (K a) (Q a) ≠ ∞) :
    Integrable (kernelLogLikelihood K Q a) (K a) :=
  (klDiv_ne_top_iff.mp hfin).2.congr (kernelLogLikelihood_eq_llr (klDiv_ne_top_iff.mp hfin).1).symm

theorem kernelLogLikelihood_integral {a : α} (hac : K a ≪ Q a) :
    (∫ b, kernelLogLikelihood K Q a b ∂K a) = (klDiv (K a) (Q a)).toReal := by
  rw [integral_congr_ae (kernelLogLikelihood_eq_llr hac)]
  exact (toReal_klDiv_of_measure_eq hac (by simp)).symm

theorem kernelLogLikelihood_norm_integral_le {a : α} (hfin : klDiv (K a) (Q a) ≠ ∞) :
    (∫ b, ‖kernelLogLikelihood K Q a b‖ ∂K a) ≤ (klDiv (K a) (Q a)).toReal+2 := by
  have he := (kernelLogLikelihood_eq_llr (klDiv_ne_top_iff.mp hfin).1).fun_comp (fun x : ℝ => ‖x‖)
  simp only [Function.comp_def] at he
  rw [integral_congr_ae he]
  exact integral_norm_llr_le hfin

theorem kernelLogLikelihood_compProd_integrable (μ : Measure α) [IsProbabilityMeasure μ]
    {C : ℝ} (hC : 0 ≤ C) (hKL : ∀ a, klDiv (K a) (Q a) ≤ ENNReal.ofReal C) :
    Integrable (Function.uncurry (kernelLogLikelihood K Q)) (μ ⊗ₘ K) := by
  have hfin (a : α) : klDiv (K a) (Q a) ≠ ∞ := (lt_of_le_of_lt (hKL a) ENNReal.ofReal_lt_top).ne
  apply (Measure.integrable_compProd_iff (kernelLogLikelihood_measurable K Q).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun a => kernelLogLikelihood_integrable (hfin a)), ?_⟩
  apply (integrable_const (C+2)).mono'
    ((kernelLogLikelihood_measurable K Q).stronglyMeasurable.norm.integral_kernel_prod_right).aestronglyMeasurable
  filter_upwards [] with a
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact (kernelLogLikelihood_norm_integral_le (hfin a)).trans
    (add_le_add_right (ENNReal.toReal_le_of_le_ofReal hC (hKL a)) 2)

theorem compProd_eq_withDensity_kernel (μ : Measure α) [IsProbabilityMeasure μ]
    (hac : ∀ a, K a ≪ Q a) :
    μ ⊗ₘ K = (μ ⊗ₘ Q).withDensity (Function.uncurry (K.rnDeriv Q)) := by
  have he : Q.withDensity (K.rnDeriv Q) = K :=
    Kernel.ext (fun a => Kernel.withDensity_rnDeriv_eq (hac a))
  change μ ⊗ₘ K = (μ ⊗ₘ Q).withDensity (fun z => K.rnDeriv Q z.1 z.2)
  rw [← Measure.compProd_withDensity (μ := μ) (κ := Q) (K.measurable_rnDeriv Q),he]

theorem compProd_llr_eq_kernel (μ : Measure α) [IsProbabilityMeasure μ]
    (hac : ∀ a, K a ≪ Q a) :
    llr (μ ⊗ₘ K) (μ ⊗ₘ Q) =ᵐ[μ ⊗ₘ K] Function.uncurry (kernelLogLikelihood K Q) := by
  have habs : μ ⊗ₘ K ≪ μ ⊗ₘ Q := Measure.AbsolutelyContinuous.compProd_right
    (Filter.Eventually.of_forall hac)
  have hr : (μ ⊗ₘ K).rnDeriv (μ ⊗ₘ Q) =ᵐ[μ ⊗ₘ Q] Function.uncurry (K.rnDeriv Q) := by
    rw [compProd_eq_withDensity_kernel μ hac]
    exact (μ ⊗ₘ Q).rnDeriv_withDensity (K.measurable_rnDeriv Q)
  filter_upwards [habs.ae_le hr] with z hz
  simp only [llr_def,kernelLogLikelihood,Function.uncurry,hz]

/-- For a common initial law, the joint relative entropy is exactly the
expected conditional relative entropy. No finite response support is assumed. -/
theorem klDiv_compProd_same_left (μ : Measure α) [IsProbabilityMeasure μ]
    {C : ℝ} (hC : 0 ≤ C) (hKL : ∀ a, klDiv (K a) (Q a) ≤ ENNReal.ofReal C) :
    klDiv (μ ⊗ₘ K) (μ ⊗ₘ Q) =
      ENNReal.ofReal (∫ a, (klDiv (K a) (Q a)).toReal ∂μ) := by
  have hfin (a : α) : klDiv (K a) (Q a) ≠ ∞ := (lt_of_le_of_lt (hKL a) ENNReal.ofReal_lt_top).ne
  have hac (a : α) := (klDiv_ne_top_iff.mp (hfin a)).1
  have hi := kernelLogLikelihood_compProd_integrable μ hC hKL
  have he := compProd_llr_eq_kernel μ hac
  rw [klDiv_of_ac_of_integrable
    (Measure.AbsolutelyContinuous.compProd_right (Filter.Eventually.of_forall hac)) (hi.congr he.symm),
    integral_congr_ae he,Measure.integral_compProd hi]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,add_sub_cancel_right]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with a
  exact kernelLogLikelihood_integral (hac a)

theorem klDiv_compProd_same_left_le (μ : Measure α) [IsProbabilityMeasure μ]
    {C : ℝ} (hC : 0 ≤ C) (hKL : ∀ a, klDiv (K a) (Q a) ≤ ENNReal.ofReal C) :
    klDiv (μ ⊗ₘ K) (μ ⊗ₘ Q) ≤ ENNReal.ofReal C := by
  rw [klDiv_compProd_same_left μ hC hKL]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ _ : α, C ∂μ := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) (integrable_const _)
      (Filter.Eventually.of_forall (fun a => ENNReal.toReal_le_of_le_ofReal hC (hKL a)))
    _ = C := by simp

end
end SecondOrder
