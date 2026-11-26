import UpperOptimization

/-!
Measure-level ingredients of the analysis-only ghost coupling.
Conditioning accepts only the basis and therefore leaves all fresh smoothing
and sample variables under their original independent product law.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Task006.Full

/-- The accepted-proposal law; it is a probability measure when the acceptance
event has positive probability. This does not define the implemented sampler. -/
noncomputable def goodRestrictedLaw {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (G : Set α) : Measure α := (μ G)⁻¹ • μ.restrict G

theorem goodRestrictedLaw_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (G : Set α) (hG : μ G ≠ 0) :
    IsProbabilityMeasure (goodRestrictedLaw μ G) where
  measure_univ := by
    simp only [goodRestrictedLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hG (measure_ne_top μ G)

theorem goodRestrictedLaw_mem {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (G : Set α) (hG : MeasurableSet G) :
    ∀ᵐ x ∂goodRestrictedLaw μ G, x ∈ G :=
  Measure.ae_smul_measure (ae_restrict_mem hG) _

theorem goodRestrictedLaw_apply {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (G S : Set α) (hS : MeasurableSet S) :
    goodRestrictedLaw μ G S = (μ G)⁻¹ * μ (S ∩ G) := by
  rw [goodRestrictedLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS]

/-- Exact product-law calculation behind the fresh-variable assertion in the
ghost paragraph: acceptance tests the basis alone, so every associated random
variable keeps its original distribution and independence. -/
theorem goodRestrictedLaw_prod_right {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν] (G : Set α) :
    goodRestrictedLaw (μ.prod ν) (G ×ˢ univ) = (goodRestrictedLaw μ G).prod ν := by
  unfold goodRestrictedLaw
  rw [Measure.prod_prod, measure_univ, mul_one, ← Measure.restrict_prod_eq_prod_univ,
    Measure.prod_smul_left]

/-- Risk transfer for actual and ghost outputs agreeing on the good event.
This proves the rare-event correction from pointwise legality and agreement;
it does not assume an inequality between their expected errors. -/
theorem coupled_expectation_transfer {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {G : Set Ω} (hG : MeasurableSet G)
    {actual ghost : Ω → ℝ} {M : ℝ}
    (ha : Integrable actual μ) (hg : Integrable ghost μ)
    (hghost : ∀ᵐ ω ∂μ, 0 ≤ ghost ω)
    (hactual : ∀ᵐ ω ∂μ, actual ω ≤ M)
    (hagree : ∀ᵐ ω ∂μ, ω ∈ G → actual ω = ghost ω) :
    (∫ ω, actual ω ∂μ) ≤ (∫ ω, ghost ω ∂μ) + M * μ.real Gᶜ := by
  have hi : Integrable (Gᶜ.indicator (fun _ : Ω => M)) μ :=
    (integrable_const M).indicator hG.compl
  have hpoint : ∀ᵐ ω ∂μ, actual ω ≤ ghost ω + Gᶜ.indicator (fun _ => M) ω := by
    filter_upwards [hghost, hactual, hagree] with ω hn hb he
    by_cases hω : ω ∈ G
    · rw [indicator_of_notMem (show ω ∉ Gᶜ by simpa using hω), add_zero]
      exact (he hω).le
    · rw [indicator_of_mem (show ω ∈ Gᶜ from hω)]
      linarith
  have hm := integral_mono_ae ha (hg.add hi) hpoint
  have heq := integral_add hg hi
  simp only [Pi.add_apply] at heq hm
  rw [heq, integral_indicator_const M hG.compl, smul_eq_mul] at hm
  simpa only [mul_comm] using hm

/-- Common-first-proposal coupling: when the first proposal is good it is kept;
otherwise the analysis-only second coordinate supplies an accepted proposal. -/
noncomputable def acceptedProposal {α : Type*} (G : Set α) (p : α × α) : α := by
  classical
  exact if p.1 ∈ G then p.1 else p.2

theorem acceptedProposal_measurable {α : Type*} [MeasurableSpace α]
    {G : Set α} (hG : MeasurableSet G) : Measurable (acceptedProposal G) := by
  classical
  exact Measurable.ite (hG.preimage measurable_fst) measurable_fst measurable_snd

/-- The coupled ghost's marginal is the normalized good-proposal law, while the
first coordinate has the original law. In particular there is no rejection
test in the actual proposal generation. -/
theorem acceptedProposal_map {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {G : Set α}
    (hG : MeasurableSet G) (hpos : μ G ≠ 0) :
    (μ.prod (goodRestrictedLaw μ G)).map (acceptedProposal G) = goodRestrictedLaw μ G := by
  classical
  letI := goodRestrictedLaw_probability μ G hpos
  ext S hS
  rw [Measure.map_apply (acceptedProposal_measurable hG) hS]
  have hpre : acceptedProposal G ⁻¹' S = ((G ∩ S) ×ˢ univ) ∪ (Gᶜ ×ˢ S) := by
    ext p
    simp only [mem_preimage, acceptedProposal, mem_union, mem_prod, mem_inter_iff,
      mem_univ, and_true, mem_compl_iff]
    split_ifs <;> tauto
  have hdisj : Disjoint ((G ∩ S) ×ˢ (univ : Set α)) (Gᶜ ×ˢ S) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact hq.1 hp.1.1
  rw [hpre, measure_union hdisj (hG.compl.prod hS), Measure.prod_prod, Measure.prod_prod,
    measure_univ, mul_one]
  have hfirst : μ (G ∩ S) = μ G * goodRestrictedLaw μ G S := by
    rw [goodRestrictedLaw_apply μ G S hS, ← mul_assoc,
      ENNReal.mul_inv_cancel hpos (measure_ne_top μ G), one_mul, inter_comm]
  rw [hfirst, ← add_mul, measure_add_measure_compl hG, measure_univ, one_mul]

theorem acceptedProposal_agrees {α : Type*} (G : Set α) (p : α × α) (hp : p.1 ∈ G) :
    acceptedProposal G p = p.1 := by
  classical
  simp only [acceptedProposal, if_pos hp]

#print axioms goodRestrictedLaw_prod_right
#print axioms coupled_expectation_transfer
#print axioms acceptedProposal_map

end Task006.Full
