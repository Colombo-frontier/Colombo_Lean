import Bilevel.StatefulMoments
import Mathlib.Probability.Kernel.CondDistrib

/-! Conditional moment assumptions hold almost everywhere in the entering
history law. This file constructs a pointwise-valid Markov kernel by changing
only null histories, rather than assuming a universal sampling seed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Bilevel.ConditionalKernelRepair
variable {State Obs Ω E : Type*} [MeasurableSpace State] [MeasurableSpace Obs]
  [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (K : Kernel State Obs) [IsMarkovKernel K]
  (error : State × Obs → E) (σ : ℝ)

def Good (s : State) : Prop :=
  Integrable (fun o => ‖error (s,o)‖ ^ 2) (K s) ∧
  (∫ o, error (s,o) ∂K s) = 0 ∧
  (∫ o, ‖error (s,o)‖ ^ 2 ∂K s) ≤ σ ^ 2

theorem good_measurable (he : Measurable error) : MeasurableSet {s | Good K error σ s} := by
  have hi := ProbabilityTheory.measurableSet_kernel_integrable
    (κ := K) (f := fun s o => ‖error (s,o)‖ ^ 2) (he.norm.pow_const 2).stronglyMeasurable
  have hm : Measurable (fun s => ∫ o, error (s,o) ∂K s) :=
    he.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hv : Measurable (fun s => ∫ o, ‖error (s,o)‖ ^ 2 ∂K s) :=
    (he.norm.pow_const 2).stronglyMeasurable.integral_kernel_prod_right'.measurable
  exact hi.inter ((measurableSet_eq_fun hm measurable_const).inter (measurableSet_le hv measurable_const))

def repair (he : Measurable error) (fallback : State → Obs) (hf : Measurable fallback) : Kernel State Obs := by
  classical
  exact Kernel.piecewise (good_measurable K error σ he) K (Kernel.deterministic fallback hf)

instance repair_markov (he : Measurable error) (fallback : State → Obs) (hf : Measurable fallback) :
    IsMarkovKernel (repair K error σ he fallback hf) := by unfold repair; infer_instance

theorem repair_good (he : Measurable error) (fallback : State → Obs) (hf : Measurable fallback)
    (hz : ∀ s, error (s,fallback s) = 0) (s : State) :
    Good (repair K error σ he fallback hf) error σ s := by
  classical
  by_cases hs : Good K error σ s
  · have heq : repair K error σ he fallback hf s = K s := by
      simp only [repair, Kernel.piecewise_apply, Set.mem_setOf_eq, if_pos hs]
    unfold Good
    rw [heq]
    exact hs
  · have hm : StronglyMeasurable (fun o => error (s,o)) :=
      (he.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
    change Integrable _ _ ∧ _ = _ ∧ _ ≤ _
    simp only [repair, Kernel.piecewise_apply, Set.mem_setOf_eq, if_neg hs, Kernel.deterministic_apply]
    refine ⟨integrable_dirac' (hm.norm.pow 2), ?_, ?_⟩
    · rw [integral_dirac' _ _ hm, hz]
    · rw [integral_dirac' (fun o => ‖error (s,o)‖ ^ 2) _ (hm.norm.pow 2), hz, norm_zero,
        zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg σ

theorem repair_ae {π : Measure State} (he : Measurable error)
    (fallback : State → Obs) (hf : Measurable fallback)
    (hg : ∀ᵐ s ∂π, Good K error σ s) :
    repair K error σ he fallback hf =ᵐ[π] K := by
  filter_upwards [hg] with s hs
  simp only [repair, Kernel.piecewise_apply, Set.mem_setOf_eq, if_pos hs]

theorem repair_compProd {π : Measure State} [IsProbabilityMeasure π] (he : Measurable error)
    (fallback : State → Obs) (hf : Measurable fallback)
    (hg : ∀ᵐ s ∂π, Good K error σ s) :
    π ⊗ₘ repair K error σ he fallback hf = π ⊗ₘ K :=
  Measure.compProd_congr (repair_ae K error σ he fallback hf hg)

variable [StandardBorelSpace Obs] [Nonempty Obs] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem conditional_good_ae (state : Ω → State) (obs : Ω → Obs)
    (hs : Measurable state) (ho : Measurable obs) (he : Measurable error)
    (hi : Integrable (fun ω => ‖error (state ω,obs ω)‖ ^ 2) μ)
    (hm : Integrable (fun ω => error (state ω,obs ω)) μ)
    (hmean : μ[fun ω => error (state ω,obs ω) | MeasurableSpace.comap state inferInstance] =ᵐ[μ] 0)
    (hvar : ∀ᵐ ω ∂μ, μ[fun ω => ‖error (state ω,obs ω)‖ ^ 2 |
      MeasurableSpace.comap state inferInstance] ω ≤ σ ^ 2) :
    ∀ᵐ s ∂μ.map state, Good (condDistrib obs state μ) error σ s := by
  let C := condDistrib obs state μ
  have hei : AEStronglyMeasurable (fun z : State × Obs => ‖error z‖ ^ 2)
      (μ.map (fun ω => (state ω,obs ω))) := (he.norm.pow_const 2).aestronglyMeasurable
  have hmap : Integrable (fun z : State × Obs => ‖error z‖ ^ 2)
      (μ.map (fun ω => (state ω,obs ω))) :=
    (integrable_map_measure hei (hs.prodMk ho).aemeasurable).mpr hi
  have hslice := (hei.ae_integrable_condDistrib_map_iff ho.aemeasurable).mpr hmap
  have hmom := condExp_prod_ae_eq_integral_condDistrib hs ho.aemeasurable he.stronglyMeasurable hm
  have hv := condExp_prod_ae_eq_integral_condDistrib hs ho.aemeasurable
    (he.norm.pow_const 2).stronglyMeasurable hi
  have hmean' : ∀ᵐ s ∂μ.map state, (∫ o, error (s,o) ∂C s) = 0 := by
    apply (ae_map_iff hs.aemeasurable
      (measurableSet_eq_fun he.stronglyMeasurable.integral_kernel_prod_right'.measurable measurable_const)).mpr
    filter_upwards [hmom,hmean] with ω heq hz
    exact heq.symm.trans hz
  have hvar' : ∀ᵐ s ∂μ.map state, (∫ o, ‖error (s,o)‖ ^ 2 ∂C s) ≤ σ ^ 2 := by
    apply (ae_map_iff hs.aemeasurable
      (measurableSet_le (he.norm.pow_const 2).stronglyMeasurable.integral_kernel_prod_right'.measurable measurable_const)).mpr
    filter_upwards [hv,hvar] with ω heq hle
    exact heq.symm ▸ hle
  filter_upwards [hslice.1,hmean',hvar'] with s hi' hm' hv'
  exact ⟨hi',hm',hv'⟩

end Bilevel.ConditionalKernelRepair
