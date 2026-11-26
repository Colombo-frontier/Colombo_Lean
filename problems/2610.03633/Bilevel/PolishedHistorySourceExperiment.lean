import Bilevel.PolishedHistoryClockProjection
import Bilevel.PolishedHistoryTerminalSelection

/-! Probability-space semantics for a deterministic public query body.
The pre-query sigma algebra may contain more information than the current
state. The final selection index is sampled independently after this body.
Conditional expectations, rather than pointwise kernel moment hypotheses,
are the admissibility fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
set_option autoImplicit false
variable {S Q O Y V : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

structure SourceExperiment (A : BorelAdaptive.Program S Q O Y)
    (tf tg : Q → V) (rf rg : O → V) (σf σg : ℝ) where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  law : Measure Ω
  [probability : IsProbabilityMeasure law]
  state : ℕ → Ω → S
  obs : ℕ → Ω → O
  state_measurable : ∀ n,Measurable (state n)
  obs_measurable : ∀ n,Measurable (obs n)
  initial : S
  init : state 0 =ᵐ[law] fun _ => initial
  next : ∀ n,∀ᵐ ω ∂law,state (n+1) ω=
    if A.halt (state n ω)=true then state n ω else A.update (state n ω,obs n ω)
  information : ℕ → MeasurableSpace Ω
  information_le : ∀ n,information n≤measurableΩ
  state_information : ∀ n,Measurable[information n] (clockedState A state n)
  upper_square_integrable : ∀ n,Integrable (fun ω => ‖rf (obs n ω)-tf (A.query (state n ω))‖^2) law
  lower_square_integrable : ∀ n,Integrable (fun ω => ‖rg (obs n ω)-tg (A.query (state n ω))‖^2) law
  upper_mean : ∀ n,law[fun ω => rf (obs n ω)-tf (A.query (state n ω)) | information n] =ᵐ[law] 0
  lower_mean : ∀ n,law[fun ω => rg (obs n ω)-tg (A.query (state n ω)) | information n] =ᵐ[law] 0
  upper_variance : ∀ n,∀ᵐ ω ∂law,law[fun ω => ‖rf (obs n ω)-tf (A.query (state n ω))‖^2 |
    information n] ω≤σf^2
  lower_variance : ∀ n,∀ᵐ ω ∂law,law[fun ω => ‖rg (obs n ω)-tg (A.query (state n ω))‖^2 |
    information n] ω≤σg^2

attribute [instance] SourceExperiment.measurableΩ SourceExperiment.probability

variable {A : BorelAdaptive.Program S Q O Y} {tf tg : Q → V} {rf rg : O → V} {σf σg : ℝ}
variable (E : SourceExperiment A tf tg rf rg σf σg)

def SourceExperiment.enter (n : ℕ) (ω : E.Ω) : Q × (S × ℕ) :=
  (A.query (E.state n ω),clockedState A E.state n ω)

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem SourceExperiment.enter_measurable (n : ℕ) : Measurable (E.enter n) :=
  (A.query_measurable.comp (E.state_measurable n)).prodMk
    (clockedState_measurable A E.state E.state_measurable n)

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem SourceExperiment.enter_information (n : ℕ) : Measurable[E.information n] (E.enter n) :=
  (A.query_measurable.comp (measurable_fst.comp (E.state_information n))).prodMk
    (E.state_information n)

variable [StandardBorelSpace O] [Nonempty O]
variable (htf : Measurable tf) (htg : Measurable tg) (hrf : Measurable rf) (hrg : Measurable rg)
  (fallback : Q → O) (hf : Measurable fallback)
  (hzf : ∀ q,rf (fallback q)=tf q) (hzg : ∀ q,rg (fallback q)=tg q)

def SourceExperiment.upperError (tf : Q → V) (rf : O → V) (z : (Q × (S × ℕ)) × O) : V := rf z.2-tf z.1.1

def SourceExperiment.lowerError (tg : Q → V) (rg : O → V) (z : (Q × (S × ℕ)) × O) : V := rg z.2-tg z.1.1

include htf hrf in
omit [StandardBorelSpace O] [Nonempty O] [NormedSpace ℝ V] [CompleteSpace V] in
theorem SourceExperiment.upperError_measurable : Measurable (SourceExperiment.upperError (S:=S) tf rf) :=
  (hrf.comp measurable_snd).sub (htf.comp (measurable_fst.comp measurable_fst))

include htg hrg in
omit [StandardBorelSpace O] [Nonempty O] [NormedSpace ℝ V] [CompleteSpace V] in
theorem SourceExperiment.lowerError_measurable : Measurable (SourceExperiment.lowerError (S:=S) tg rg) :=
  (hrg.comp measurable_snd).sub (htg.comp (measurable_fst.comp measurable_fst))

def SourceExperiment.repairedKernel (n : ℕ) : Kernel (Q × (S × ℕ)) O :=
  conditionalPairedKernel (μ:=E.law) (E.enter n) (E.obs n)
    (SourceExperiment.upperError tf rf) (SourceExperiment.lowerError tg rg) σf σg
    (SourceExperiment.upperError_measurable htf hrf) (SourceExperiment.lowerError_measurable htg hrg)
    (fun z => fallback z.1) (hf.comp measurable_fst)

instance SourceExperiment.repairedKernel_markov (n : ℕ) :
    IsMarkovKernel (E.repairedKernel htf htg hrf hrg fallback hf n) := by
  unfold SourceExperiment.repairedKernel
  infer_instance

include hzf hzg in
/-- Pointwise moment validity and exact joint-law preservation follow from
the manuscript's original conditional expectations on the actual sigma algebra. -/
theorem SourceExperiment.repairedKernel_represents (n : ℕ) :
    (∀ s,ConditionalKernelRepair.Good (E.repairedKernel htf htg hrf hrg fallback hf n)
      (SourceExperiment.upperError tf rf) σf s ∧
      ConditionalKernelRepair.Good (E.repairedKernel htf htg hrf hrg fallback hf n)
      (SourceExperiment.lowerError tg rg) σg s) ∧
    (E.law.map (E.enter n)) ⊗ₘ E.repairedKernel htf htg hrf hrg fallback hf n=
      E.law.map (fun ω => (E.enter n ω,E.obs n ω)) := by
  have hmf := conditional_moments_coarsen (E.enter n) (E.information n)
    (E.information_le n) (E.enter_information n)
    (fun ω => rf (E.obs n ω)-tf (A.query (E.state n ω))) σf (E.upper_mean n) (E.upper_variance n)
  have hmg := conditional_moments_coarsen (E.enter n) (E.information n)
    (E.information_le n) (E.enter_information n)
    (fun ω => rg (E.obs n ω)-tg (A.query (E.state n ω))) σg (E.lower_mean n) (E.lower_variance n)
  have hfi : Integrable (fun ω => rf (E.obs n ω)-tf (A.query (E.state n ω))) E.law :=
    ((memLp_two_iff_integrable_sq_norm
      ((hrf.comp (E.obs_measurable n)).sub
        (htf.comp (A.query_measurable.comp (E.state_measurable n)))).aestronglyMeasurable).mpr
      (E.upper_square_integrable n)).integrable (by norm_num)
  have hgi : Integrable (fun ω => rg (E.obs n ω)-tg (A.query (E.state n ω))) E.law :=
    ((memLp_two_iff_integrable_sq_norm
      ((hrg.comp (E.obs_measurable n)).sub
        (htg.comp (A.query_measurable.comp (E.state_measurable n)))).aestronglyMeasurable).mpr
      (E.lower_square_integrable n)).integrable (by norm_num)
  exact one_call_paired_representation (E.enter n) (E.obs n)
    (E.enter_measurable n) (E.obs_measurable n)
    (SourceExperiment.upperError tf rf) (SourceExperiment.lowerError tg rg) σf σg
    (SourceExperiment.upperError_measurable htf hrf) (SourceExperiment.lowerError_measurable htg hrg)
    (fun z => fallback z.1) (hf.comp measurable_fst)
    (fun z => by change rf (fallback z.1)-tf z.1=0; rw [hzf,sub_self])
    (fun z => by change rg (fallback z.1)-tg z.1=0; rw [hzg,sub_self])
    (E.upper_square_integrable n) (E.lower_square_integrable n) hfi hgi hmf.1 hmg.1 hmf.2 hmg.2

end Bilevel.PolishedHistory
