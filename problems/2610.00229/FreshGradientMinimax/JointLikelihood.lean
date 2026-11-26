import FreshGradientMinimax.JointDensity
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! The likelihood ratio of an adaptive transition is the product of the
old-state likelihood ratio and the measurable conditional likelihood ratio. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]
  {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {K J : Kernel α β} [IsMarkovKernel K] [IsMarkovKernel J]

def kernelLLR (K J : Kernel α β) [IsMarkovKernel K] [IsMarkovKernel J]
    (z : α × β) : ℝ := Real.log ((K.rnDeriv J z.1 z.2).toReal)

theorem kernelLLR_measurable : Measurable (kernelLLR K J) :=
  ((K.measurable_rnDeriv J).ennreal_toReal).log

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
theorem kernelLLR_eq_llr {a : α} (ha : K a ≪ J a) :
    (fun b => kernelLLR K J (a, b)) =ᵐ[K a] llr (K a) (J a) := by
  filter_upwards [ha.ae_le (K.rnDeriv_eq_rnDeriv_measure (η := J))] with b hb
  simp only [kernelLLR, llr, hb]

theorem compProd_rnDeriv (hPQ : P ≪ Q) (hKJ : ∀ a, K a ≪ J a) :
    (P ⊗ₘ K).rnDeriv (Q ⊗ₘ J) =ᵐ[Q ⊗ₘ J]
      (fun z => P.rnDeriv Q z.1 * K.rnDeriv J z.1 z.2) := by
  have he := compProd_density (P.measurable_rnDeriv Q) (K.measurable_rnDeriv J)
    (P.withDensity_rnDeriv_eq Q hPQ) (fun a => by
      rw [withDensity_congr_ae (K.rnDeriv_eq_rnDeriv_measure (η := J))]
      exact (K a).withDensity_rnDeriv_eq (J a) (hKJ a))
  rw [he]
  exact (Q ⊗ₘ J).rnDeriv_withDensity
    (((P.measurable_rnDeriv Q).comp measurable_fst).mul (K.measurable_rnDeriv J))

theorem compProd_llr (hPQ : P ≪ Q) (hKJ : ∀ a, K a ≪ J a) :
    llr (P ⊗ₘ K) (Q ⊗ₘ J) =ᵐ[P ⊗ₘ K]
      (fun z => llr P Q z.1 + kernelLLR K J z) := by
  have hac := hPQ.compProd (Filter.Eventually.of_forall hKJ)
  have hp : ∀ᵐ z ∂(P ⊗ₘ K), 0 < (P.rnDeriv Q z.1).toReal := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_lt measurable_const ((P.measurable_rnDeriv Q).comp measurable_fst).ennreal_toReal)
    filter_upwards [Measure.rnDeriv_pos hPQ, hPQ.ae_le (P.rnDeriv_ne_top Q)] with a ha ht
    exact Filter.Eventually.of_forall (fun _ => ENNReal.toReal_pos ha.ne' ht)
  have hk : ∀ᵐ z ∂(P ⊗ₘ K), 0 < (K.rnDeriv J z.1 z.2).toReal := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_lt measurable_const (K.measurable_rnDeriv J).ennreal_toReal)
    exact Filter.Eventually.of_forall (fun a => Kernel.rnDeriv_toReal_pos (hKJ a))
  filter_upwards [hac.ae_le (compProd_rnDeriv hPQ hKJ), hp, hk] with z hz hpz hkz
  simp only [llr, hz, ENNReal.toReal_mul, kernelLLR]
  exact Real.log_mul hpz.ne' hkz.ne'

end FreshGradientMinimax
