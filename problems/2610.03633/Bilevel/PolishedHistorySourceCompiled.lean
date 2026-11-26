import Bilevel.PolishedHistorySourceOperational
import Bilevel.PolishedCompiledHistoryLaw

/-! Original conditional-expectation experiments of a compiled deterministic
query body inherit its verified history-kernel denotation. The repaired
kernel is constructed from that experiment, rather than supplied as an
admissibility assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
set_option autoImplicit false
open OracleCode Stateful

theorem trajectoryLaw_dirac_start {S Q O Y H I : Type*} [MeasurableSpace S]
    [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
    [MeasurableSpace H] [MeasurableSpace I]
    (P : BorelAdaptive.Program S Q O Y) (R : HistoryProgram.Oracle Q O H)
    (start : I → S) (hs : Measurable start) (a : I) (h : H) :
    HistoryProgram.trajectoryLaw P R (Measure.dirac a) start h=
      HistoryProgram.trajectoryLaw P R (Measure.dirac (start a)) id h := by
  have hp : Measurable (fun a => HistoryProgram.initialPrefix (start a,h)) :=
    HistoryProgram.initialPrefix_measurable.comp (hs.prodMk measurable_const)
  have hq : Measurable (fun s : S => HistoryProgram.initialPrefix (id s,h)) :=
    HistoryProgram.initialPrefix_measurable.comp (measurable_id.prodMk measurable_const)
  rw [HistoryProgram.trajectoryLaw,HistoryProgram.trajectoryLaw,
    Measure.map_dirac hp,Measure.map_dirac hq]
  rfl

variable {Q O Inp B : Space} [StandardBorelSpace O] [Nonempty O]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (q₀ : Q) (o₀ : O) (c : Code Q O Inp B)
  {tf tg : Q → V} {rf rg : O → V} {σf σg : ℝ}
  (E : SourceExperiment (compile q₀ o₀ c).program tf tg rf rg σf σg)
  (htf : Measurable tf) (htg : Measurable tg) (hrf : Measurable rf) (hrg : Measurable rg)
  (fallback : Q → O) (hf : Measurable fallback)
  (hzf : ∀ q,rf (fallback q)=tf q) (hzg : ∀ q,rg (fallback q)=tg q)
  (a : Inp) (hinit : E.initial=(compile q₀ o₀ c).start a)

include hinit in
theorem SourceExperiment.compiled_initial_law :
    E.repairedExecution htf htg hrf hrg fallback hf=
      HistoryProgram.trajectoryLaw (compile q₀ o₀ c).program
        (E.repairedOracle htf htg hrf hrg fallback hf)
        (Measure.dirac a) (compile q₀ o₀ c).start (E.initial,0) := by
  rw [trajectoryLaw_dirac_start _ _ _ (compile q₀ o₀ c).start_measurable,←hinit]
  rfl

include hzf hzg hinit in
/-- Source actual original calls are bounded by the verified compositional
denotation of the same compiled code under its constructed repaired law. -/
theorem SourceExperiment.compiled_cost_le_denote :
    E.actualCost≤∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote (H:=of ((compile q₀ o₀ c).state × ℕ))
        (E.repairedOracle htf htg hrf hrg fallback hf).law
        (E.repairedOracle htf htg hrf hrg fallback hf).update
        (E.repairedOracle htf htg hrf hrg fallback hf).update_measurable c).law (a,(E.initial,0)) := by
  have hb := PolishedCompiledHistory.compiled_stopped_calls_le
    (H:=of ((compile q₀ o₀ c).state × ℕ))
    (E.repairedOracle htf htg hrf hrg fallback hf) q₀ o₀ c (Measure.dirac a) (E.initial,0)
  rw [← E.compiled_initial_law q₀ o₀ c htf htg hrf hrg fallback hf a hinit,
    E.repaired_cost_eq_actual htf htg hrf hrg fallback hf hzf hzg] at hb
  have hm : Measurable (fun a => ∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote (H:=of ((compile q₀ o₀ c).state × ℕ))
        (E.repairedOracle htf htg hrf hrg fallback hf).law
        (E.repairedOracle htf htg hrf hrg fallback hf).update
        (E.repairedOracle htf htg hrf hrg fallback hf).update_measurable c).law (a,(E.initial,0))) :=
    ((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
      (measurable_snd.comp measurable_snd)).lintegral_kernel.comp
        (measurable_id.prodMk measurable_const)
  rwa [lintegral_dirac' a hm] at hb

include hzf hzg hinit in
/-- The actual abstract first-halt output has exactly the code denotation's
output distribution whenever the proved denotation call expectation is finite. -/
theorem SourceExperiment.compiled_output_law
    (hcost : (∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote (H:=of ((compile q₀ o₀ c).state × ℕ))
        (E.repairedOracle htf htg hrf hrg fallback hf).law
        (E.repairedOracle htf htg hrf hrg fallback hf).update
        (E.repairedOracle htf htg hrf hrg fallback hf).update_measurable c).law (a,(E.initial,0)))≠⊤) :
    E.law.map (fun ω => HistoryProgram.stoppedOutput (compile q₀ o₀ c).program
      (experimentPath E.state ω))=
    ((OracleCode.History.denote (H:=of ((compile q₀ o₀ c).state × ℕ))
      (E.repairedOracle htf htg hrf hrg fallback hf).law
      (E.repairedOracle htf htg hrf hrg fallback hf).update
      (E.repairedOracle htf htg hrf hrg fallback hf).update_measurable c).law (a,(E.initial,0))).map Prod.fst := by
  have hb := E.compiled_cost_le_denote q₀ o₀ c htf htg hrf hrg fallback hf hzf hzg a hinit
  have he : (∫⁻ w,HistoryProgram.totalCalls (compile q₀ o₀ c).program w
      ∂E.repairedExecution htf htg hrf hrg fallback hf)≠⊤ := by
    rw [E.repaired_cost_eq_actual htf htg hrf hrg fallback hf hzf hzg]
    exact ne_top_of_le_ne_top hcost hb
  rw [←E.repaired_output_law htf htg hrf hrg fallback hf hzf hzg he,
    E.compiled_initial_law q₀ o₀ c htf htg hrf hrg fallback hf a hinit]
  exact PolishedCompiledHistory.compiled_stopped_output_law _ _ _ _ _ _ hcost

include hzf hzg hinit in
/-- A fresh independent terminal selector has exactly the same actual
selected-output distribution as the verified code denotation. -/
theorem SourceExperiment.compiled_terminal_law {I Z : Type*} [MeasurableSpace I]
    [MeasurableSpace Z] (ρ : Measure I) [SFinite ρ]
    (select : I × B → Z) (hselect : Measurable select)
    (hcost : (∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote (H:=of ((compile q₀ o₀ c).state × ℕ))
        (E.repairedOracle htf htg hrf hrg fallback hf).law
        (E.repairedOracle htf htg hrf hrg fallback hf).update
        (E.repairedOracle htf htg hrf hrg fallback hf).update_measurable c).law (a,(E.initial,0)))≠⊤) :
    (ρ.prod E.law).map (fun z => select (z.1,
      HistoryProgram.stoppedOutput (compile q₀ o₀ c).program (experimentPath E.state z.2)))=
    (ρ.prod ((OracleCode.History.denote (H:=of ((compile q₀ o₀ c).state × ℕ))
      (E.repairedOracle htf htg hrf hrg fallback hf).law
      (E.repairedOracle htf htg hrf hrg fallback hf).update
      (E.repairedOracle htf htg hrf hrg fallback hf).update_measurable c).law (a,(E.initial,0)))).map
      (fun z => select (z.1,z.2.1)) := by
  exact independent_terminal_selection_law ρ _ _ _ _
    ((HistoryProgram.stoppedOutput_measurable _).comp (experimentPath_measurable E.state E.state_measurable))
    measurable_fst
    (E.compiled_output_law q₀ o₀ c htf htg hrf hrg fallback hf hzf hzg a hinit hcost)
    select hselect

include hzf hzg hinit in
/-- Equality of actual terminal risk on the original probability space and
on the compositional history-kernel denotation. -/
theorem SourceExperiment.compiled_terminal_risk_eq {I Z : Type*} [MeasurableSpace I]
    [MeasurableSpace Z] (ρ : Measure I) [SFinite ρ]
    (select : I × B → Z) (hselect : Measurable select)
    (loss : Z → ℝ≥0∞) (hloss : Measurable loss)
    (hcost : (∫⁻ y,(y.2.2:ℝ≥0∞)
      ∂(OracleCode.History.denote (H:=of ((compile q₀ o₀ c).state × ℕ))
        (E.repairedOracle htf htg hrf hrg fallback hf).law
        (E.repairedOracle htf htg hrf hrg fallback hf).update
        (E.repairedOracle htf htg hrf hrg fallback hf).update_measurable c).law (a,(E.initial,0)))≠⊤) :
    (∫⁻ z,loss (select (z.1,
      HistoryProgram.stoppedOutput (compile q₀ o₀ c).program (experimentPath E.state z.2))) ∂ρ.prod E.law)=
    ∫⁻ z,loss (select (z.1,z.2.1))
      ∂ρ.prod ((OracleCode.History.denote (H:=of ((compile q₀ o₀ c).state × ℕ))
        (E.repairedOracle htf htg hrf hrg fallback hf).law
        (E.repairedOracle htf htg hrf hrg fallback hf).update
        (E.repairedOracle htf htg hrf hrg fallback hf).update_measurable c).law (a,(E.initial,0))) := by
  have he := E.compiled_terminal_law q₀ o₀ c htf htg hrf hrg fallback hf hzf hzg a hinit
    ρ select hselect hcost
  have hs : Measurable (fun z : I × E.Ω => select (z.1,
      HistoryProgram.stoppedOutput (compile q₀ o₀ c).program (experimentPath E.state z.2))) :=
    hselect.comp (measurable_fst.prodMk (((HistoryProgram.stoppedOutput_measurable _).comp
      (experimentPath_measurable E.state E.state_measurable)).comp measurable_snd))
  have hk : Measurable (fun z : I × Outcome B ((compile q₀ o₀ c).state × ℕ) => select (z.1,z.2.1)) :=
    hselect.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact (lintegral_map hloss hs).symm.trans
    ((congrArg (fun ν : Measure Z => ∫⁻ z,loss z ∂ν) he).trans (lintegral_map hloss hk))

end Bilevel.PolishedHistory
