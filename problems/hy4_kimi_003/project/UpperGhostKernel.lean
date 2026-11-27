import UpperOptimizationCoupling

/-! Measurable state-dependent normalized-good kernels for the paper's
analysis-only ghost sampler. The actual proposal retains its original law. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace Task006.Full

noncomputable def goodProposalKernel {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : X → Set B)
    (hG : MeasurableSet {p : X × B | p.2 ∈ G p.1}) : Kernel X B where
  toFun x := goodRestrictedLaw μ (G x)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [goodRestrictedLaw_apply μ _ S hS]
    have hden : Measurable (fun x => μ (G x)) :=
      measurable_measure_prodMk_left hG
    have hnum : Measurable (fun x => μ (S ∩ G x)) := by
      have h := measurable_measure_prodMk_left (hG.inter (hS.preimage measurable_snd)) (ν := μ)
      convert h using 1
      funext x
      congr 1
      ext b
      simp only [mem_inter_iff, mem_preimage, mem_setOf_eq]
      tauto
    exact hden.inv.mul hnum

@[simp] theorem goodProposalKernel_apply {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : X → Set B)
    (hG : MeasurableSet {p : X × B | p.2 ∈ G p.1}) (x : X) :
    goodProposalKernel μ G hG x = goodRestrictedLaw μ (G x) := rfl

theorem goodProposalKernel_markov {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : X → Set B)
    (hG : MeasurableSet {p : X × B | p.2 ∈ G p.1}) (hpos : ∀ x, μ (G x) ≠ 0) :
    IsMarkovKernel (goodProposalKernel μ G hG) :=
  ⟨fun x => goodRestrictedLaw_probability μ (G x) (hpos x)⟩

theorem goodProposalKernel_support {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : X → Set B)
    (hG : MeasurableSet {p : X × B | p.2 ∈ G p.1}) (x : X) :
    ∀ᵐ b ∂goodProposalKernel μ G hG x, b ∈ G x :=
  goodRestrictedLaw_mem μ (G x) (hG.preimage measurable_prodMk_left)

theorem adaptiveAcceptedProposal_measurable {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (G : X → Set B) (hG : MeasurableSet {p : X × B | p.2 ∈ G p.1}) :
    Measurable (fun z : X × (B × B) => acceptedProposal (G z.1) z.2) := by
  classical
  exact Measurable.ite (hG.preimage (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)

#print axioms goodProposalKernel
#print axioms adaptiveAcceptedProposal_measurable

end Task006.Full
