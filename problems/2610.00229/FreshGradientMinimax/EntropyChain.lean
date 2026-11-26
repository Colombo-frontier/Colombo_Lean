import FreshGradientMinimax.JointLikelihood
import FreshGradientMinimax.EntropyNorm

/-! A chain bound for arbitrary measurable state spaces and countably
generated response spaces. Integrability follows from the conditional KL
bound itself, so queries and stored states may be unbounded. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]
  {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {K J : Kernel α β} [IsMarkovKernel K] [IsMarkovKernel J]

theorem kernelLLR_compProd_integrable {c : ℝ} (hc : 0 ≤ c)
    (hK : ∀ a, klDiv (K a) (J a) ≤ ENNReal.ofReal c) :
    Integrable (kernelLLR K J) (P ⊗ₘ K) := by
  have hb a := finite_kl_information_bound hc (hK a)
  have he a := kernelLLR_eq_llr (hb a).1
  apply (Measure.integrable_compProd_iff kernelLLR_measurable.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun a => (hb a).2.1.congr (he a).symm), ?_⟩
  apply (integrable_const (c + 2)).mono'
    (kernelLLR_measurable.stronglyMeasurable.norm.integral_kernel_prod_right').aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  have hne : (fun b => ‖kernelLLR K J (a, b)‖) =ᵐ[K a]
      (fun b => ‖llr (K a) (J a) b‖) := (he a).mono (fun _ h => congrArg norm h)
  rw [integral_congr_ae hne]
  exact (hb a).2.2.2

theorem compProd_information_bound (hPQ : P ≪ Q) (hi : Integrable (llr P Q) P)
    {c : ℝ} (hc : 0 ≤ c) (hK : ∀ a, klDiv (K a) (J a) ≤ ENNReal.ofReal c) :
    (P ⊗ₘ K) ≪ (Q ⊗ₘ J) ∧ Integrable (llr (P ⊗ₘ K) (Q ⊗ₘ J)) (P ⊗ₘ K) ∧
      (∫ z, llr (P ⊗ₘ K) (Q ⊗ₘ J) z ∂(P ⊗ₘ K)) ≤ (∫ a, llr P Q a ∂P) + c := by
  have hb a := finite_kl_information_bound hc (hK a)
  have hKJ a := (hb a).1
  have he := compProd_llr hPQ hKJ
  have hi1 : Integrable (fun z : α × β => llr P Q z.1) (P ⊗ₘ K) := by
    apply (Measure.integrable_compProd_iff (f := fun z : α × β => llr P Q z.1)
      ((measurable_llr P Q).comp measurable_fst).aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun a => integrable_const (llr P Q a)), ?_⟩
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hi.norm
  have hi2 := kernelLLR_compProd_integrable (P := P) hc hK
  have hij : Integrable (llr (P ⊗ₘ K) (Q ⊗ₘ J)) (P ⊗ₘ K) := (hi1.add hi2).congr he.symm
  refine ⟨hPQ.compProd (Filter.Eventually.of_forall hKJ), hij, ?_⟩
  rw [integral_congr_ae he, integral_add hi1 hi2,
    Measure.integral_compProd hi1, Measure.integral_compProd hi2]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]
  apply add_le_add_left
  have hic : Integrable (fun a => ∫ b, kernelLLR K J (a, b) ∂K a) P := by
    apply (integrable_const (c + 2)).mono'
      kernelLLR_measurable.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro a
    apply (norm_integral_le_integral_norm _).trans
    have hne : (fun b => ‖kernelLLR K J (a, b)‖) =ᵐ[K a]
        (fun b => ‖llr (K a) (J a) b‖) :=
      (kernelLLR_eq_llr (hKJ a)).mono (fun _ h => congrArg norm h)
    rw [integral_congr_ae hne]
    exact (hb a).2.2.2
  have hle := integral_mono hic (integrable_const c) (fun a => by
    rw [integral_congr_ae (kernelLLR_eq_llr (hKJ a))]
    exact (hb a).2.2.1)
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hle

theorem compProd_kl_bound {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hPQ : klDiv P Q ≤ ENNReal.ofReal b)
    (hK : ∀ a, klDiv (K a) (J a) ≤ ENNReal.ofReal c) :
    klDiv (P ⊗ₘ K) (Q ⊗ₘ J) ≤ ENNReal.ofReal (b + c) := by
  obtain ⟨ha, hi, hb', _⟩ := finite_kl_information_bound hb hPQ
  obtain ⟨ha', hi', hc'⟩ := compProd_information_bound ha hi hc hK
  rw [klDiv_of_ac_of_integrable ha' hi']
  simp only [measureReal_univ_eq_one, add_sub_cancel_right]
  exact ENNReal.ofReal_le_ofReal (hc'.trans (add_le_add_right hb' c))

end FreshGradientMinimax

