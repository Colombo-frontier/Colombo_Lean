import MatchingBounds1005.KernelKL

/-!
# Integrability from actual conditional relative entropy bounds

The negative log-likelihood tail is controlled using the reverse
Radon-Nikodym derivative. Thus bounded finite conditional KL is sufficient
for the joint log-likelihood integrability needed in the chain rule.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace MatchingBounds1005.KernelKLIntegrability
open KernelKL

theorem integral_norm_llr_le {α : Type*} [MeasurableSpace α]
    {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hi : Integrable (llr P Q) P) :
    (∫ x, ‖llr P Q x‖ ∂P) ≤ (klDiv P Q).toReal + 2 := by
  have hrev : Integrable (fun x => (Q.rnDeriv P x).toReal) P := by
    simpa using Measure.integrableOn_toReal_rnDeriv (μ := Q) (ν := P)
      (s := Set.univ) (measure_ne_top Q Set.univ)
  have hexp : Integrable (fun x => Real.exp (-llr P Q x)) P :=
    hrev.congr (exp_neg_llr hPQ).symm
  have he : (∫ x, Real.exp (-llr P Q x) ∂P) ≤ 1 := by
    rw [integral_congr_ae (exp_neg_llr hPQ)]
    simpa using Measure.setIntegral_toReal_rnDeriv_le (μ := Q) (ν := P)
      (s := Set.univ) (measure_ne_top Q Set.univ)
  have hp (t : ℝ) : ‖t‖ ≤ t + 2 * Real.exp (-t) := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith [Real.add_one_le_exp (-t), Real.exp_pos (-t)]
  have hb := integral_mono_ae hi.norm (hi.add (hexp.const_mul 2))
    (ae_of_all P (fun x => hp (llr P Q x)))
  change (∫ x, ‖llr P Q x‖ ∂P) ≤ ∫ x, llr P Q x + 2 * Real.exp (-llr P Q x) ∂P at hb
  rw [integral_add hi (hexp.const_mul 2), integral_const_mul] at hb
  rw [toReal_klDiv_of_measure_eq hPQ (by simp)]
  linarith

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSpace.CountableOrCountablyGenerated α β]
variable (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]

/-- A uniform bound on actual conditional KL discharges the joint
log-likelihood integrability obligation. -/
theorem integrable_kernelLLR_of_bounded_kl (P : Measure α) [IsProbabilityMeasure P]
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ a, klDiv (κ a) (η a) ≤ ENNReal.ofReal C) :
    Integrable (kernelLLR κ η) (P ⊗ₘ κ) := by
  have hfinite (a : α) : klDiv (κ a) (η a) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hc a)
  have hAC (a : α) : κ a ≪ η a := (klDiv_ne_top_iff.mp (hfinite a)).1
  have hInt (a : α) : Integrable (llr (κ a) (η a)) (κ a) :=
    (klDiv_ne_top_iff.mp (hfinite a)).2
  have hfiber (a : α) : Integrable (fun b => kernelLLR κ η (a, b)) (κ a) :=
    (hInt a).congr (kernelLLR_eq_llr κ η hAC a).symm
  have hbound (a : α) : (∫ b, ‖kernelLLR κ η (a, b)‖ ∂κ a) ≤ C + 2 := by
    have hn : (fun b => ‖kernelLLR κ η (a, b)‖) =ᵐ[κ a]
        (fun b => ‖llr (κ a) (η a) b‖) :=
      (kernelLLR_eq_llr κ η hAC a).fun_comp (fun x : ℝ => ‖x‖)
    rw [integral_congr_ae hn]
    have hc' : (klDiv (κ a) (η a)).toReal ≤ C := by
      simpa only [ENNReal.toReal_ofReal hC] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hc a)
    exact (integral_norm_llr_le (hAC a) (hInt a)).trans (by linarith)
  have hmeas : StronglyMeasurable
      (fun a => ∫ b, ‖kernelLLR κ η (a, b)‖ ∂κ a) :=
    (kernelLLR_measurable κ η).norm.stronglyMeasurable.integral_kernel_prod_right'
  have houter : Integrable (fun a => ∫ b, ‖kernelLLR κ η (a, b)‖ ∂κ a) P := by
    apply (integrable_const (C + 2)).mono' hmeas.aestronglyMeasurable
    exact ae_of_all P (fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact hbound a)
  exact (Measure.integrable_compProd_iff
    (kernelLLR_measurable κ η).aestronglyMeasurable).mpr
      ⟨ae_of_all P hfiber, houter⟩

end MatchingBounds1005.KernelKLIntegrability
