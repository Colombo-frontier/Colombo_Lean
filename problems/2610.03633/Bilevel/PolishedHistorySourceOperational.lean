import Bilevel.PolishedHistorySourceExperiment

/-! End-to-end operational Markovization of source-admissible deterministic
query experiments. Conditional expectations on the original information
produce one repaired fixed-initial-history oracle, with exact actual
stopping cost and finite-cost stopped output law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
set_option autoImplicit false
variable {S Q O Y V : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [StandardBorelSpace O] [Nonempty O]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {A : BorelAdaptive.Program S Q O Y} {tf tg : Q → V} {rf rg : O → V} {σf σg : ℝ}
variable (E : SourceExperiment A tf tg rf rg σf σg)
  (htf : Measurable tf) (htg : Measurable tg) (hrf : Measurable rf) (hrg : Measurable rg)
  (fallback : Q → O) (hf : Measurable fallback)
  (hzf : ∀ q,rf (fallback q)=tf q) (hzg : ∀ q,rg (fallback q)=tg q)

def SourceExperiment.repairedOracle : HistoryProgram.Oracle Q O (S × ℕ) :=
  deterministicHistoryOracle (clockedProgram A)
    (E.repairedKernel htf htg hrf hrg fallback hf) Prod.snd measurable_snd

include hzf hzg in
/-- The single clock-selected oracle satisfies both moment bounds at every
query and hidden state after simultaneous null-state repair. -/
theorem SourceExperiment.repairedOracle_good (q : Q) (h : S × ℕ) :
    ConditionalKernelRepair.Good (E.repairedOracle htf htg hrf hrg fallback hf).law
      (SourceExperiment.upperError tf rf) σf (q,h) ∧
    ConditionalKernelRepair.Good (E.repairedOracle htf htg hrf hrg fallback hf).law
      (SourceExperiment.lowerError tg rg) σg (q,h) := by
  exact (E.repairedKernel_represents htf htg hrf hrg fallback hf hzf hzg h.2).1 (q,h)

def SourceExperiment.repairedExecution : Measure (HistoryProgram.Path S (S × ℕ)) :=
  HistoryProgram.trajectoryLaw A (E.repairedOracle htf htg hrf hrg fallback hf)
    (Measure.dirac E.initial) id (E.initial,0)

instance SourceExperiment.repairedExecution_probability :
    IsProbabilityMeasure (E.repairedExecution htf htg hrf hrg fallback hf) :=
  HistoryProgram.trajectoryLaw_probability _ _ _ _ measurable_id _

def SourceExperiment.actualCost : ℝ≥0∞ :=
  ∫⁻ ω,HistoryProgram.totalCalls A (experimentPath E.state ω) ∂E.law

def SourceExperiment.actualRisk (loss : Y → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput A (experimentPath E.state ω))) ∂E.law

omit [StandardBorelSpace O] [Nonempty O] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] in
theorem SourceExperiment.clocked_init :
    clockedState A E.state 0 =ᵐ[E.law] fun _ => (E.initial,0) := by
  filter_upwards [E.init] with ω hω
  exact Prod.ext hω rfl

include hzf hzg in
/-- Exact preservation of expected original calls, including infinity. -/
theorem SourceExperiment.repaired_cost_eq_actual :
    (∫⁻ w,HistoryProgram.totalCalls A w
      ∂E.repairedExecution htf htg hrf hrg fallback hf)=E.actualCost := by
  rw [SourceExperiment.repairedExecution]
  refine (clocked_execution_cost A (E.repairedOracle htf htg hrf hrg fallback hf)
    E.initial 0 (E.initial,0)).trans ?_
  exact deterministic_experiment_stopped_cost (clockedProgram A)
    (clockedState A E.state) E.obs
    (clockedState_measurable A E.state E.state_measurable) E.obs_measurable
    (E.repairedKernel htf htg hrf hrg fallback hf)
    (fun n => (E.repairedKernel_represents htf htg hrf hrg fallback hf hzf hzg n).2)
    Prod.snd measurable_snd (clockedState_live_clock A E.state E.obs E.next)
    (clockedState_next A E.state E.obs E.next) (E.initial,0) E.clocked_init

include hzf hzg in
/-- A finite original-call budget preserves every measurable first-halt
output risk between the source probability-space and repaired executions. -/
theorem SourceExperiment.repaired_risk_eq_actual (loss : Y → ℝ) (hloss : Measurable loss)
    (hcost : (∫⁻ w,HistoryProgram.totalCalls A w
      ∂E.repairedExecution htf htg hrf hrg fallback hf)≠⊤) :
    (∫⁻ w,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput A w))
      ∂E.repairedExecution htf htg hrf hrg fallback hf)=E.actualRisk loss := by
  have hclockcost : (∫⁻ w,HistoryProgram.totalCalls (clockedProgram A) w
      ∂HistoryProgram.trajectoryLaw (clockedProgram A)
        (E.repairedOracle htf htg hrf hrg fallback hf)
        (Measure.dirac (E.initial,0)) id (E.initial,0))≠⊤ := by
    rw [← clocked_execution_cost A]
    exact hcost
  refine (clocked_execution_risk A (E.repairedOracle htf htg hrf hrg fallback hf)
    E.initial 0 (E.initial,0) loss hloss hcost).trans ?_
  exact deterministic_experiment_stopped_risk (clockedProgram A)
    (clockedState A E.state) E.obs
    (clockedState_measurable A E.state E.state_measurable) E.obs_measurable
    (E.repairedKernel htf htg hrf hrg fallback hf)
    (fun n => (E.repairedKernel_represents htf htg hrf hrg fallback hf hzf hzg n).2)
    Prod.snd measurable_snd (clockedState_live_clock A E.state E.obs E.next)
    (clockedState_next A E.state E.obs E.next) (E.initial,0) E.clocked_init
    loss hloss hclockcost

include hzf hzg in
/-- The complete stopped output law is preserved under the source
conditional-moment assumptions, with a fixed initial hidden history. -/
theorem SourceExperiment.repaired_output_law
    (hcost : (∫⁻ w,HistoryProgram.totalCalls A w
      ∂E.repairedExecution htf htg hrf hrg fallback hf)≠⊤) :
    (E.repairedExecution htf htg hrf hrg fallback hf).map (HistoryProgram.stoppedOutput A)=
      E.law.map (fun ω => HistoryProgram.stoppedOutput A (experimentPath E.state ω)) := by
  apply Measure.ext
  intro t ht
  let loss : Y → ℝ := t.indicator (fun _ => 1)
  have hloss : Measurable loss := measurable_const.indicator ht
  have he := E.repaired_risk_eq_actual htf htg hrf hrg fallback hf hzf hzg loss hloss hcost
  have htest : ∀ y,ENNReal.ofReal (loss y)=t.indicator (fun _ => (1:ℝ≥0∞)) y := by
    intro y
    by_cases hy : y∈t <;> simp [loss,Set.indicator_of_mem,Set.indicator_of_not_mem,hy]
  change _=(∫⁻ ω,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput A (experimentPath E.state ω))) ∂E.law) at he
  simp_rw [htest] at he
  have hmap : Measurable (fun ω => HistoryProgram.stoppedOutput A (experimentPath E.state ω)) :=
    (HistoryProgram.stoppedOutput_measurable A).comp (experimentPath_measurable E.state E.state_measurable)
  rw [← lintegral_map (measurable_const.indicator ht) (HistoryProgram.stoppedOutput_measurable A),
    ← lintegral_map (measurable_const.indicator ht) hmap] at he
  exact (lintegral_indicator_one ht).symm.trans (he.trans (lintegral_indicator_one ht))

include hzf hzg in
/-- A terminal independent private index is added only after all queries.
Its complete selected-output law remains identical in the repaired model. -/
theorem SourceExperiment.terminal_selection_law {I Z : Type*} [MeasurableSpace I]
    [MeasurableSpace Z] (ρ : Measure I) [SFinite ρ]
    (select : I × Y → Z) (hselect : Measurable select)
    (hcost : (∫⁻ w,HistoryProgram.totalCalls A w
      ∂E.repairedExecution htf htg hrf hrg fallback hf)≠⊤) :
    (ρ.prod (E.repairedExecution htf htg hrf hrg fallback hf)).map
      (fun z => select (z.1,HistoryProgram.stoppedOutput A z.2))=
    (ρ.prod E.law).map
      (fun z => select (z.1,HistoryProgram.stoppedOutput A (experimentPath E.state z.2))) := by
  exact independent_terminal_selection_law ρ _ _ _ _
    (HistoryProgram.stoppedOutput_measurable A)
    ((HistoryProgram.stoppedOutput_measurable A).comp (experimentPath_measurable E.state E.state_measurable))
    (E.repaired_output_law htf htg hrf hrg fallback hf hzf hzg hcost) select hselect

end Bilevel.PolishedHistory
