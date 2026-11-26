import Bilevel.ConditionalKernelRepair

/-! Simultaneous repair of the two original full-gradient conditional laws.
The same joint observation law is retained off a null set of histories;
in particular no independence of the two responses is introduced. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Bilevel.ConditionalKernelRepair
variable {State Obs Ω E : Type*} [MeasurableSpace State] [MeasurableSpace Obs]
  [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem deterministic_good (error : State × Obs → E) (σ : ℝ) (he : Measurable error)
    (fallback : State → Obs) (hf : Measurable fallback)
    (hz : ∀ s, error (s,fallback s) = 0) (s : State) :
    Good (Kernel.deterministic fallback hf) error σ s := by
  have hm : StronglyMeasurable (fun o => error (s,o)) :=
    (he.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
  simp only [Good, Kernel.deterministic_apply]
  refine ⟨integrable_dirac' (hm.norm.pow 2), ?_, ?_⟩
  · rw [integral_dirac' _ _ hm, hz]
  · rw [integral_dirac' (fun o => ‖error (s,o)‖ ^ 2) _ (hm.norm.pow 2), hz, norm_zero,
      zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg σ

def repairPair (K : Kernel State Obs) [IsMarkovKernel K]
    (ef eg : State × Obs → E) (σf σg : ℝ) (hef : Measurable ef) (heg : Measurable eg)
    (fallback : State → Obs) (hf : Measurable fallback) : Kernel State Obs := by
  classical
  exact Kernel.piecewise ((good_measurable K ef σf hef).inter (good_measurable K eg σg heg))
    K (Kernel.deterministic fallback hf)

instance repairPair_markov (K : Kernel State Obs) [IsMarkovKernel K]
    (ef eg : State × Obs → E) (σf σg : ℝ) (hef : Measurable ef) (heg : Measurable eg)
    (fallback : State → Obs) (hf : Measurable fallback) :
    IsMarkovKernel (repairPair K ef eg σf σg hef heg fallback hf) := by
  unfold repairPair
  infer_instance

theorem repairPair_good (K : Kernel State Obs) [IsMarkovKernel K]
    (ef eg : State × Obs → E) (σf σg : ℝ) (hef : Measurable ef) (heg : Measurable eg)
    (fallback : State → Obs) (hf : Measurable fallback)
    (hzf : ∀ s, ef (s,fallback s) = 0) (hzg : ∀ s, eg (s,fallback s) = 0) (s : State) :
    Good (repairPair K ef eg σf σg hef heg fallback hf) ef σf s ∧
    Good (repairPair K ef eg σf σg hef heg fallback hf) eg σg s := by
  classical
  by_cases hs : Good K ef σf s ∧ Good K eg σg s
  · have heq : repairPair K ef eg σf σg hef heg fallback hf s = K s := by
      simp only [repairPair, Kernel.piecewise_apply, Set.mem_inter_iff, Set.mem_setOf_eq, if_pos hs]
    simp only [Good, heq]
    exact hs
  · have heq : repairPair K ef eg σf σg hef heg fallback hf s = (Kernel.deterministic fallback hf) s := by
      simp only [repairPair, Kernel.piecewise_apply, Set.mem_inter_iff, Set.mem_setOf_eq, if_neg hs]
    simp only [Good, heq]
    exact ⟨deterministic_good ef σf hef fallback hf hzf s, deterministic_good eg σg heg fallback hf hzg s⟩

theorem repairPair_compProd (K : Kernel State Obs) [IsMarkovKernel K]
    (ef eg : State × Obs → E) (σf σg : ℝ) (hef : Measurable ef) (heg : Measurable eg)
    (fallback : State → Obs) (hf : Measurable fallback)
    {π : Measure State} [IsProbabilityMeasure π]
    (hgf : ∀ᵐ s ∂π, Good K ef σf s) (hgg : ∀ᵐ s ∂π, Good K eg σg s) :
    π ⊗ₘ repairPair K ef eg σf σg hef heg fallback hf = π ⊗ₘ K := by
  classical
  apply Measure.compProd_congr
  filter_upwards [hgf,hgg] with s hsf hsg
  simp only [repairPair, Kernel.piecewise_apply, Set.mem_inter_iff, Set.mem_setOf_eq,
    if_pos (And.intro hsf hsg)]

end Bilevel.ConditionalKernelRepair
