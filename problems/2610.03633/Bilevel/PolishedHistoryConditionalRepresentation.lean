import Bilevel.ConditionalKernelPair
import Bilevel.HistorySFOFull
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! Regular conditional distributions realize the manuscript's paired
conditional moment assumptions on an arbitrary probability space. Null
conditioning states are repaired by the exact response. The same joint
response law is preserved, including the correlation of the two vectors.
This is a one-call and a family-of-calls representation theorem; it does not
assume a universal sampling seed or independent upper/lower responses. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedHistory
set_option autoImplicit false

variable {State Obs Ω E : Type*} [MeasurableSpace State] [MeasurableSpace Obs]
  [StandardBorelSpace Obs] [Nonempty Obs] [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The repaired RCD is determined by the actual joint experiment. -/
def conditionalPairedKernel (state : Ω → State) (obs : Ω → Obs)
    (ef eg : State × Obs → E) (σf σg : ℝ)
    (hef : Measurable ef) (heg : Measurable eg)
    (fallback : State → Obs) (hf : Measurable fallback) : Kernel State Obs :=
  ConditionalKernelRepair.repairPair (condDistrib obs state μ) ef eg σf σg hef heg fallback hf

instance conditionalPairedKernel_markov (state : Ω → State) (obs : Ω → Obs)
    (ef eg : State × Obs → E) (σf σg : ℝ)
    (hef : Measurable ef) (heg : Measurable eg)
    (fallback : State → Obs) (hf : Measurable fallback) :
    IsMarkovKernel (conditionalPairedKernel (μ:=μ) state obs ef eg σf σg hef heg fallback hf) := by
  unfold conditionalPairedKernel
  infer_instance

/-- Conditional expectations relative to all entering information become a
pointwise-valid paired kernel, without changing the actual joint experiment.
`state` may contain the full transcript, the adaptive query, and private
randomness. Only the finite-dimensional observation requires standard Borel. -/
theorem one_call_paired_representation
    (state : Ω → State) (obs : Ω → Obs) (hs : Measurable state) (ho : Measurable obs)
    (ef eg : State × Obs → E) (σf σg : ℝ)
    (hef : Measurable ef) (heg : Measurable eg)
    (fallback : State → Obs) (hf : Measurable fallback)
    (hzf : ∀ s,ef (s,fallback s)=0) (hzg : ∀ s,eg (s,fallback s)=0)
    (hif : Integrable (fun ω => ‖ef (state ω,obs ω)‖^2) μ)
    (hig : Integrable (fun ω => ‖eg (state ω,obs ω)‖^2) μ)
    (hmf : Integrable (fun ω => ef (state ω,obs ω)) μ)
    (hmg : Integrable (fun ω => eg (state ω,obs ω)) μ)
    (hmef : μ[fun ω => ef (state ω,obs ω) | MeasurableSpace.comap state inferInstance] =ᵐ[μ] 0)
    (hmeg : μ[fun ω => eg (state ω,obs ω) | MeasurableSpace.comap state inferInstance] =ᵐ[μ] 0)
    (hvf : ∀ᵐ ω ∂μ, μ[fun ω => ‖ef (state ω,obs ω)‖^2 |
      MeasurableSpace.comap state inferInstance] ω≤σf^2)
    (hvg : ∀ᵐ ω ∂μ, μ[fun ω => ‖eg (state ω,obs ω)‖^2 |
      MeasurableSpace.comap state inferInstance] ω≤σg^2) :
    let K := conditionalPairedKernel (μ:=μ) state obs ef eg σf σg hef heg fallback hf
    (∀ s,ConditionalKernelRepair.Good K ef σf s ∧
      ConditionalKernelRepair.Good K eg σg s) ∧
    (μ.map state) ⊗ₘ K=μ.map (fun ω => (state ω,obs ω)) := by
  dsimp only
  refine ⟨fun s => ConditionalKernelRepair.repairPair_good
    (condDistrib obs state μ) ef eg σf σg hef heg fallback hf hzf hzg s,?_⟩
  have hgf := ConditionalKernelRepair.conditional_good_ae
    ef σf state obs hs ho hef hif hmf hmef hvf
  have hgg := ConditionalKernelRepair.conditional_good_ae
    eg σg state obs hs ho heg hig hmg hmeg hvg
  haveI : IsProbabilityMeasure (μ.map state) := isProbabilityMeasure_map hs.aemeasurable
  unfold conditionalPairedKernel
  rw [ConditionalKernelRepair.repairPair_compProd _ _ _ _ _ _ _ _ _ hgf hgg]
  exact compProd_map_condDistrib ho.aemeasurable

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Conditional moment bounds remain valid after forgetting private or
historical information, provided the retained entering state is measurable
in the original pre-query information. This is the tower property, not an
independence assumption. -/
theorem conditional_moments_coarsen
    (state : Ω → State) (mF : MeasurableSpace Ω)
    (hmF : mF ≤ mΩ) (hsF : Measurable[mF] state)
    (error : Ω → E) (σ : ℝ)
    (hmean : μ[error | mF] =ᵐ[μ] 0)
    (hvar : ∀ᵐ ω ∂μ, μ[fun ω => ‖error ω‖^2 | mF] ω≤σ^2) :
    (μ[error | MeasurableSpace.comap state inferInstance] =ᵐ[μ] 0) ∧
    (∀ᵐ ω ∂μ, μ[fun ω => ‖error ω‖^2 |
      MeasurableSpace.comap state inferInstance] ω≤σ^2) := by
  let mS := MeasurableSpace.comap state inferInstance
  have hmS : mS ≤ mF := hsF.comap_le
  constructor
  · calc
      μ[error | mS] =ᵐ[μ] μ[μ[error | mF] | mS] :=
        (condExp_condExp_of_le (μ:=μ) (f:=error) hmS hmF).symm
      _ =ᵐ[μ] μ[0 | mS] := condExp_congr_ae (m:=mS) hmean
      _ =ᵐ[μ] 0 := by rw [condExp_zero]
  · have hv := condExp_mono (μ:=μ) (m:=mS)
      (f:=μ[fun ω => ‖error ω‖^2 | mF]) (g:=fun _ => σ^2)
      integrable_condExp (integrable_const _) hvar
    have ht := condExp_condExp_of_le (μ:=μ) (f:=fun ω => ‖error ω‖^2) hmS hmF
    rw [condExp_const (μ:=μ) (hmS.trans hmF)] at hv
    filter_upwards [hv,ht] with ω hω heq
    exact heq ▸ hω

omit [StandardBorelSpace Obs] [Nonempty Obs] in
/-- A deterministic history update after the same paired response preserves
its original distribution. No independence assumption is introduced. -/
theorem disintegration_update_law {Next : Type*} [MeasurableSpace Next]
    (state : Ω → State) (obs : Ω → Obs) (hs : Measurable state) (ho : Measurable obs)
    (K : Kernel State Obs) [IsMarkovKernel K]
    (hK : (μ.map state) ⊗ₘ K=μ.map (fun ω => (state ω,obs ω)))
    (update : State × Obs → Next) (hu : Measurable update) :
    Stateful.KernelMap.dependent K update ∘ₘ (μ.map state)=
      μ.map (fun ω => update (state ω,obs ω)) := by
  haveI : IsProbabilityMeasure (μ.map state) := isProbabilityMeasure_map hs.aemeasurable
  rw [Stateful.KernelMap.dependent,← Measure.map_comp _ _ hu,
    ← Measure.compProd_eq_comp_prod,hK,Measure.map_map hu (hs.prodMk ho)]
  rfl

section Family
variable {T : Type*} [MeasurableSpace T]

/-- The operational distributions obtained by iterating the reconstructed
conditional kernels from the actual entering-state law. -/
def reconstructedRun (K : ℕ → Kernel T Obs) (update : ℕ → T × Obs → T)
    (initial : Measure T) : ℕ → Measure T
  | 0 => initial
  | n+1 => Stateful.KernelMap.dependent (K n) (update n) ∘ₘ reconstructedRun K update initial n

omit [StandardBorelSpace Obs] [Nonempty Obs] in
/-- All finite-horizon state marginals of an actual adaptive experiment are
preserved by its conditional kernels. The initial state is the actual random
state, so it can retain arbitrarily correlated private information. -/
theorem reconstructedRun_eq_actual
    (state : ℕ → Ω → T) (obs : ℕ → Ω → Obs)
    (hs : ∀ n,Measurable (state n)) (ho : ∀ n,Measurable (obs n))
    (K : ℕ → Kernel T Obs) [∀ n,IsMarkovKernel (K n)]
    (hK : ∀ n,(μ.map (state n)) ⊗ₘ K n=
      μ.map (fun ω => (state n ω,obs n ω)))
    (update : ℕ → T × Obs → T) (hu : ∀ n,Measurable (update n))
    (hnext : ∀ n, (fun ω => update n (state n ω,obs n ω)) =ᵐ[μ] state (n+1))
    (n : ℕ) :
    reconstructedRun K update (μ.map (state 0)) n=μ.map (state n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [reconstructedRun,ih,disintegration_update_law (state n) (obs n)
        (hs n) (ho n) (K n) (hK n) (update n) (hu n)]
      exact Measure.map_congr (hnext n)

end Family

end Bilevel.PolishedHistory
