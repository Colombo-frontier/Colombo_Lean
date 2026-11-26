import Nonsmooth.RecursiveMeanMoments
import Nonsmooth.ResponseHistoryAugmentation
import Nonsmooth.SupportPosteriorKernel

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)]
  {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

theorem policy_recursive_belief_at_response (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    let u := policyResponseQuery (k := k) p ω
    let hu := fun j => policyResponseQuery_measurable (k := k) p hp ω j
    ∀ᵐ a ∂Q, recursiveSupportBelief Q u hu n (recursiveSupportResponse u n a) =
      supportPosteriorKernel Q p ω n (supportAugmentedTranscript p a ω n) := by
  let u := policyResponseQuery (k := k) p ω
  have hu : ∀ j, Measurable (u j) := fun j => policyResponseQuery_measurable p hp ω j
  let X := recursiveSupportResponse u n
  let Z : (Fin k → E) → SupportHistory E k n := fun a => supportAugmentedTranscript p a ω n
  have hX : Measurable X := recursiveSupportResponse_measurable u hu n
  have hZ : Measurable Z := (supportAugmentedTranscript_measurable p hp n).comp
    (measurable_id.prodMk measurable_const)
  have hK := conditionalKernel_reencoding Q X hX id measurable_id Z hZ
    (responseHistoryAugment u n) (responseHistoryAugment_measurable u hu n)
    supportResponseErase (supportResponseErase_measurable n)
    (fun a => (responseHistoryAugment_policy p ω n a).symm)
    (fun a => (recursiveSupportResponse_policy p ω n a).symm)
    (recursiveSupportBelief Q u hu n) (recursiveSupportBelief_ae_condDistrib Q u hu n)
  filter_upwards [ae_of_ae_map hZ.aemeasurable hK] with a ha
  change recursiveSupportBelief Q u hu n (supportResponseErase (supportAugmentedTranscript p a ω n)) =
    supportPosteriorKernel Q p ω n (supportAugmentedTranscript p a ω n) at ha
  rw [← recursiveSupportResponse_policy] at ha
  exact ha

theorem policy_aggregate_mean_ae_recursive (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (hi : Integrable (fun a : Fin k → E => ∑ i, a i) Q)
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    let u := policyResponseQuery (k := k) p ω
    let hu := fun j => policyResponseQuery_measurable (k := k) p hp ω j
    Q[fun a : Fin k → E => ∑ i, a i | supportTranscriptInformation p ω n] =ᵐ[Q]
      fun a => recursiveSupportMean Q u hu n (recursiveSupportResponse u n a) := by
  filter_upwards [supportPosteriorKernel_aggregate_mean Q p hp ω n hi,
    policy_recursive_belief_at_response Q p hp ω n] with a ha hK
  change _ = ∫ b : Fin k → E, ∑ i, b i ∂_ at ha ⊢
  rw [hK]
  exact ha

end
end Nonsmooth
