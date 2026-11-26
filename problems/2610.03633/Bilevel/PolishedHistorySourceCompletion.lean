import Bilevel.PolishedHistorySourceExperiment
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! Oracle observations have no operational role after halt. Completing
those unused observations by the exact response converts live-call moment
conditions to the all-time sequence convention used by SourceExperiment,
without changing any actual program state, output, or original calls. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedHistory
set_option autoImplicit false
variable {Ω V : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- The source's conditional unbiasedness equation and the centered-error
form used by SourceExperiment are equivalent for a pre-query-measurable
true gradient and integrable displayed conditional expectations. -/
theorem conditional_centered_iff_unbiased (mF : MeasurableSpace Ω) (hmF : mF≤mΩ)
    (sample truth : Ω → V) (hs : Integrable sample μ) (ht : Integrable truth μ)
    (htF : StronglyMeasurable[mF] truth) :
    (μ[fun ω => sample ω-truth ω | mF] =ᵐ[μ] 0) ↔
      (μ[sample | mF] =ᵐ[μ] truth) := by
  have hsub := condExp_sub hs ht mF
  rw [condExp_of_stronglyMeasurable hmF htF ht] at hsub
  constructor
  · intro hz
    filter_upwards [hsub,hz] with ω heq hzero
    exact sub_eq_zero.mp (heq.symm.trans hzero)
  · intro hm
    filter_upwards [hsub,hm] with ω heq hmean
    simpa only [Pi.sub_apply,hmean,sub_self,Pi.zero_apply] using heq

/-- Moments are required only on the event that a call is made. Zero
completion outside that pre-query-measurable event preserves the bounds. -/
theorem conditional_live_completion (mF : MeasurableSpace Ω)
    (live : Set Ω) (hLive : MeasurableSet[mF] live)
    (error : Ω → V) (he : @Measurable Ω V mΩ _ error)
    (hi : Integrable (fun ω => ‖error ω‖^2) μ) (σ : ℝ)
    (hmean : ∀ᵐ ω ∂μ,ω∈live → μ[error | mF] ω=0)
    (hvar : ∀ᵐ ω ∂μ,ω∈live → μ[fun ω => ‖error ω‖^2 | mF] ω≤σ^2) :
    (μ[live.indicator error | mF] =ᵐ[μ] 0) ∧
    (∀ᵐ ω ∂μ,μ[fun ω => ‖live.indicator error ω‖^2 | mF] ω≤σ^2) := by
  have hm : Integrable error μ :=
    ((memLp_two_iff_integrable_sq_norm (μ:=μ) he.aestronglyMeasurable).mpr hi).integrable (by norm_num)
  have hmCE := condExp_indicator hm hLive
  have hvCE := condExp_indicator hi hLive
  have hsq : (fun ω => ‖live.indicator error ω‖^2)=
      live.indicator (fun ω => ‖error ω‖^2) := by
    funext ω
    by_cases hω : ω∈live <;> simp [Set.indicator_of_mem,Set.indicator_of_not_mem,hω]
  rw [hsq]
  constructor
  · filter_upwards [hmCE,hmean] with ω hω hz
    by_cases hl : ω∈live
    · simpa only [Set.indicator_of_mem hl,hz hl,Pi.zero_apply] using hω
    · simpa only [Set.indicator_of_not_mem hl,Pi.zero_apply] using hω
  · filter_upwards [hvCE,hvar] with ω hω hv
    by_cases hl : ω∈live
    · rw [Set.indicator_of_mem hl] at hω
      exact hω.trans_le (hv hl)
    · rw [Set.indicator_of_not_mem hl] at hω
      exact hω.le.trans (sq_nonneg σ)

section Observation
variable {S Q O Y : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]
  (A : BorelAdaptive.Program S Q O Y)

def completeObservation (fallback : Q → O) (state : Ω → S) (obs : Ω → O) (ω : Ω) : O :=
  if A.halt (state ω)=true then fallback (A.query (state ω)) else obs ω

theorem completeObservation_measurable (fallback : Q → O) (hf : Measurable fallback)
    (state : Ω → S) (hs : Measurable state) (obs : Ω → O) (ho : Measurable obs) :
    Measurable (completeObservation A fallback state obs) :=
  (hf.comp (A.query_measurable.comp hs)).ite
    ((A.halt_measurable.comp hs) (measurableSet_singleton true)) ho

omit mΩ [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [NormedSpace ℝ V] [CompleteSpace V] in
theorem completeObservation_error (fallback : Q → O) (truth : Q → V) (read : O → V)
    (hz : ∀ q,read (fallback q)=truth q) (state : Ω → S) (obs : Ω → O) :
    (fun ω => read (completeObservation A fallback state obs ω)-truth (A.query (state ω)))=
      {ω | A.halt (state ω)=false}.indicator (fun ω => read (obs ω)-truth (A.query (state ω))) := by
  funext ω
  cases hh : A.halt (state ω) with
  | true => simp [completeObservation,hh,hz]
  | false => simp [completeObservation,hh]

omit mΩ [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [NormedSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup V] in
theorem completeObservation_next (fallback : Q → O) (state : Ω → S) (obs : Ω → O) (ω : Ω) :
    (if A.halt (state ω)=true then state ω else
      A.update (state ω,completeObservation A fallback state obs ω))=
    (if A.halt (state ω)=true then state ω else A.update (state ω,obs ω)) := by
  cases hh : A.halt (state ω) <;> simp [completeObservation,hh]

end Observation
end Bilevel.PolishedHistory
