import Bilevel.PolishedHistorySourceModel

/-! Source algorithms have an arbitrary randomized query body followed by
an independent terminal random choice. The oracle never sees that future
terminal draw. Ordinary randomized Borel algorithms are included. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery PrimitiveGeometry Stateful BorelAdaptive
set_option autoImplicit false
set_option maxHeartbeats 1200000

structure PostAlgorithm (G : Geometry) where
  Private : Type
  State : Type
  Output : Type
  Terminal : Type
  [measurablePrivate : MeasurableSpace Private]
  [measurableState : MeasurableSpace State]
  [measurableOutput : MeasurableSpace Output]
  [measurableTerminal : MeasurableSpace Terminal]
  privateLaw : Measure Private
  [privateProbability : IsProbabilityMeasure privateLaw]
  body : BorelAdaptive.Program State (G.X × G.Y) (FullResponse G.X G.Y) Output
  start : Private → State
  start_measurable : Measurable start
  terminalLaw : Measure Terminal
  [terminalProbability : IsProbabilityMeasure terminalLaw]
  select : Terminal × Output → G.X
  select_measurable : Measurable select

attribute [instance] PostAlgorithm.measurablePrivate PostAlgorithm.measurableState
  PostAlgorithm.measurableOutput PostAlgorithm.measurableTerminal
  PostAlgorithm.privateProbability PostAlgorithm.terminalProbability

namespace PostAlgorithm
variable {G : Geometry} (P : PostAlgorithm G)

def packedBody : BorelAdaptive.Program P.State G.Query G.Reply P.Output where
  query s:=pack (P.body.query s).1 (P.body.query s).2
  query_measurable:=packLinear.continuous.measurable.comp P.body.query_measurable
  update z:=P.body.update (z.1,splitResponse z.2)
  update_measurable:=P.body.update_measurable.comp (measurable_fst.prodMk (splitResponse_measurable.comp measurable_snd))
  halt:=P.body.halt
  halt_measurable:=P.body.halt_measurable
  output:=P.body.output
  output_measurable:=P.body.output_measurable

/-- Same actual body dynamics; the dummy output is used only to reuse the
random-initial source-execution record, whose cost ignores outputs. -/
def bodyAsAlgorithm : Algorithm G where
  Private:=P.Private
  State:=P.State
  privateLaw:=P.privateLaw
  program:={ P.packedBody with output:=fun _ => 0, output_measurable:=measurable_const }
  start:=P.start
  start_measurable:=P.start_measurable

/-- Presampling an independent terminal seed yields an ordinary Borel
algorithm for the stationary fresh subclass. Body queries ignore it. -/
def compile : Algorithm G where
  Private:=P.Private × P.Terminal
  State:=P.State × P.Terminal
  privateLaw:=P.privateLaw.prod P.terminalLaw
  program:={
    query:=fun s => P.packedBody.query s.1
    query_measurable:=P.packedBody.query_measurable.comp measurable_fst
    update:=fun z => (P.packedBody.update (z.1.1,z.2),z.1.2)
    update_measurable:=(P.packedBody.update_measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk (measurable_snd.comp measurable_fst)
    halt:=fun s => P.packedBody.halt s.1
    halt_measurable:=P.packedBody.halt_measurable.comp measurable_fst
    output:=fun s => P.select (s.2,P.body.output s.1)
    output_measurable:=P.select_measurable.comp
      (measurable_snd.prodMk (P.body.output_measurable.comp measurable_fst)) }
  start:=fun p => (P.start p.1,p.2)
  start_measurable:=(P.start_measurable.comp measurable_fst).prodMk measurable_snd

end PostAlgorithm

abbrev PostSolverAt := (G : Geometry) → G.X → G.Y → PostAlgorithm G

namespace SourceRandomExecution
variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable {M : SourceMean G μ L ρ Δ R₀} {P : PostAlgorithm G}
variable (E : SourceRandomExecution M P.bodyAsAlgorithm σf σg)

theorem path_measurable : Measurable E.path :=
  measurable_pi_lambda _ (fun n => (E.state_measurable n).prodMk measurable_const)

def postOutput (z : P.Terminal × E.Ω) : G.X :=
  P.select (z.1,HistoryProgram.stoppedOutput P.packedBody (E.path z.2))

theorem postOutput_measurable : Measurable E.postOutput :=
  P.select_measurable.comp (measurable_fst.prodMk
    (((HistoryProgram.stoppedOutput_measurable P.packedBody).comp E.path_measurable).comp measurable_snd))

def postRisk : ℝ≥0∞ :=
  ∫⁻ z,ENNReal.ofReal (M.loss (E.postOutput z)) ∂P.terminalLaw.prod E.law

end SourceRandomExecution

variable {μ L ρ Δ R₀ σf σg : ℝ}

structure PostSourceChallenge (A : PostSolverAt) (μ L ρ Δ R₀ σf σg : ℝ) where
  geometry : Geometry
  mean : SourceMean geometry μ L ρ Δ R₀
  execution : SourceRandomExecution mean (A geometry mean.x₀ mean.yinit).bodyAsAlgorithm σf σg

def postSourceAccurate (conservative : Bool) (ε : ℝ) (A : PostSolverAt) : Prop :=
  ∀ C : PostSourceChallenge A μ L ρ Δ R₀ σf σg,
    (conservative=true → C.execution.IsConservative) → C.execution.postRisk≤ENNReal.ofReal ε

def postSourceWorstCost (conservative : Bool) (A : PostSolverAt) : ℝ≥0∞ :=
  ⨆ C : {C : PostSourceChallenge A μ L ρ Δ R₀ σf σg // conservative=true → C.execution.IsConservative},C.val.execution.cost

def postSourceComplexity (conservative : Bool) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ A : {A : PostSolverAt // postSourceAccurate (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) conservative ε A},
    postSourceWorstCost (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) conservative A.val

end Bilevel.PolishedHistory
