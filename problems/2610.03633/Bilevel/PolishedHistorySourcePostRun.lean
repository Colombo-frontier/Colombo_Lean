import Bilevel.PolishedHistorySourcePost

/-! Arbitrary independent terminal selections compile to ordinary randomized
Borel algorithms without changing any stationary fresh call or output law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery PrimitiveGeometry Stateful BorelAdaptive
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) (P : PostAlgorithm G)

theorem post_compile_run (p : P.Private) (t : P.Terminal)
    (draws : IndependentStream.Stream I.Seed) (n : ℕ) :
    BorelAdaptive.run P.compile.program I.reply () draws (P.compile.start (p,t)) n=
      (BorelAdaptive.run P.bodyAsAlgorithm.program I.reply () draws (P.start p) n,t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [BorelAdaptive.run,BorelAdaptive.run,ih]
    unfold BorelAdaptive.step
    change (if P.packedBody.halt _ then (_,t) else (P.packedBody.update (_,_),t))=
      ((if P.packedBody.halt _ then _ else P.packedBody.update (_,_)),t)
    split_ifs <;> rfl

theorem post_compile_halt_run (p : P.Private) (t : P.Terminal)
    (draws : IndependentStream.Stream I.Seed) (n : ℕ) :
    P.compile.program.halt (BorelAdaptive.run P.compile.program I.reply () draws (P.compile.start (p,t)) n)=
      P.bodyAsAlgorithm.program.halt (BorelAdaptive.run P.bodyAsAlgorithm.program I.reply () draws (P.start p) n) := by
  rw [post_compile_run I P]
  rfl

theorem post_compile_stopTime (p : P.Private) (t : P.Terminal) (draws : IndependentStream.Stream I.Seed) :
    BorelAdaptive.stopTime P.compile.program I.reply ((),(P.compile.start (p,t),draws))=
      BorelAdaptive.stopTime P.bodyAsAlgorithm.program I.reply ((),(P.start p,draws)) := by
  classical
  unfold BorelAdaptive.stopTime BorelAdaptive.Terminated
  simp only [post_compile_halt_run I P]

theorem post_compile_calls (p : P.Private) (t : P.Terminal) (draws : IndependentStream.Stream I.Seed) :
    BorelAdaptive.seededCalls P.compile.program I.reply P.compile.start ((),((p,t),draws))=
      HistoryProgram.totalCalls P.bodyAsAlgorithm.program (freshSourcePath I P.bodyAsAlgorithm (p,draws)) := by
  classical
  change BorelAdaptive.totalCalls P.compile.program I.reply ((),(P.compile.start (p,t),draws))=
    BorelAdaptive.totalCalls P.bodyAsAlgorithm.program I.reply ((),(P.start p,draws))
  unfold BorelAdaptive.totalCalls BorelAdaptive.Terminated
  simp only [post_compile_halt_run I P,post_compile_stopTime I P]

theorem post_compile_output (p : P.Private) (t : P.Terminal) (draws : IndependentStream.Stream I.Seed) :
    (BorelAdaptive.seededStopped P.compile.program I.reply P.compile.start ((),((p,t),draws))).2=
      (stationarySourceExecution I P.bodyAsAlgorithm).postOutput (t,(p,draws)) := by
  change P.compile.program.output (BorelAdaptive.run P.compile.program I.reply () draws (P.compile.start (p,t))
    (BorelAdaptive.stopTime P.compile.program I.reply ((),(P.compile.start (p,t),draws))))=_
  rw [post_compile_stopTime I P,post_compile_run I P]
  rfl

/-- The actual permutation moves the presampled terminal seed after the
entire body experiment. It preserves the full product probability law. -/
theorem post_private_permutation_preserving :
    MeasurePreserving (fun z : (P.Private × P.Terminal) × IndependentStream.Stream I.Seed =>
      (z.1.2,(z.1.1,z.2)))
      ((P.privateLaw.prod P.terminalLaw).prod (IndependentStream.law I.law))
      (P.terminalLaw.prod (freshSourceLaw I P.bodyAsAlgorithm)) := by
  exact (measurePreserving_prodAssoc P.terminalLaw P.privateLaw (IndependentStream.law I.law)).comp
    ((Measure.measurePreserving_swap (μ:=P.privateLaw) (ν:=P.terminalLaw)).prod
      (MeasurePreserving.id (IndependentStream.law I.law)))

private theorem postCost_integrand_measurable :
    Measurable (fun z : P.Terminal × FreshSourceSpace I P.bodyAsAlgorithm =>
      HistoryProgram.totalCalls P.bodyAsAlgorithm.program (freshSourcePath I P.bodyAsAlgorithm z.2)) :=
  ((HistoryProgram.totalCalls_measurable P.bodyAsAlgorithm.program).comp
    ((seedPath_measurable I P.bodyAsAlgorithm))).comp measurable_snd

private theorem postRisk_integrand_measurable :
    Measurable (fun z : P.Terminal × FreshSourceSpace I P.bodyAsAlgorithm =>
      ENNReal.ofReal (I.loss ((stationarySourceExecution I P.bodyAsAlgorithm).postOutput z))) :=
  (I.loss_measurable.comp (SourceRandomExecution.postOutput_measurable (P:=P) (stationarySourceExecution I P.bodyAsAlgorithm))).ennreal_ofReal

/-- Exact original-call expectation, including infinity. No accuracy or
finite-cost premise is required. -/
theorem post_compile_cost : I.cost P.compile=(stationarySourceExecution I P.bodyAsAlgorithm).cost := by
  let f : P.Terminal × FreshSourceSpace I P.bodyAsAlgorithm → ℝ≥0∞ := fun z =>
    HistoryProgram.totalCalls P.bodyAsAlgorithm.program (freshSourcePath I P.bodyAsAlgorithm z.2)
  have hp := post_private_permutation_preserving I P
  have hm : Measurable f := postCost_integrand_measurable I P
  have hmap := lintegral_map (μ:=(P.privateLaw.prod P.terminalLaw).prod (IndependentStream.law I.law)) hm hp.measurable
  rw [hp.map_eq] at hmap
  change (∫⁻ z,BorelAdaptive.seededCalls P.compile.program I.reply P.compile.start ((),z)
    ∂(P.privateLaw.prod P.terminalLaw).prod (IndependentStream.law I.law))=_
  have he : (fun z : (P.Private × P.Terminal) × IndependentStream.Stream I.Seed =>
      BorelAdaptive.seededCalls P.compile.program I.reply P.compile.start ((),z))=
      fun z => f (z.1.2,(z.1.1,z.2)) := by
    funext z
    exact post_compile_calls I P z.1.1 z.1.2 z.2
  rw [he,← hmap]
  change (∫⁻ z,f z ∂P.terminalLaw.prod (freshSourceLaw I P.bodyAsAlgorithm))=_
  rw [lintegral_prod _ hm.aemeasurable]
  simp only [f,lintegral_const,measure_univ,one_mul,mul_one]
  rfl

/-- Exact stopped output risk with the independent terminal draw. It also
holds on nontermination, with the same source stopping-time convention. -/
theorem post_compile_risk : I.risk P.compile=(stationarySourceExecution I P.bodyAsAlgorithm).postRisk := by
  let f : P.Terminal × FreshSourceSpace I P.bodyAsAlgorithm → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (I.loss ((stationarySourceExecution I P.bodyAsAlgorithm).postOutput z))
  have hp := post_private_permutation_preserving I P
  have hm : Measurable f := postRisk_integrand_measurable I P
  have hmap := lintegral_map (μ:=(P.privateLaw.prod P.terminalLaw).prod (IndependentStream.law I.law)) hm hp.measurable
  rw [hp.map_eq] at hmap
  change (∫⁻ z,ENNReal.ofReal (I.loss (BorelAdaptive.seededStopped P.compile.program I.reply P.compile.start ((),z)).2)
    ∂(P.privateLaw.prod P.terminalLaw).prod (IndependentStream.law I.law))=_
  have he : (fun z : (P.Private × P.Terminal) × IndependentStream.Stream I.Seed =>
      ENNReal.ofReal (I.loss (BorelAdaptive.seededStopped P.compile.program I.reply P.compile.start ((),z)).2))=
      fun z => f (z.1.2,(z.1.1,z.2)) := by
    funext z
    rcases z with ⟨⟨p,t⟩,draws⟩
    rw [post_compile_output I P p t draws]
  rw [he,← hmap]
  rfl

end Bilevel.PolishedHistory
