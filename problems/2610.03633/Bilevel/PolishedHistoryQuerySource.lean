import Bilevel.PolishedSourcePostClasses

/-! Direct source semantics with only the queried point adapted to the
pre-query information. Hidden algorithm state and unused private randomness
need not be measurable in that information. State recursion is the actual
pointwise program execution, not an added oracle assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery PrimitiveGeometry BorelAdaptive
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {μ L ρ Δ R₀ σf σg : ℝ}

structure QuerySourceExecution {G : Geometry} (M : SourceMean G μ L ρ Δ R₀)
    (A : Algorithm G) (σf σg : ℝ) where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  law : Measure Ω
  [probability : IsProbabilityMeasure law]
  privateSeed : Ω → A.Private
  private_measurable : Measurable privateSeed
  private_law : law.map privateSeed=A.privateLaw
  state : ℕ → Ω → A.State
  obs : ℕ → Ω → G.Reply
  sample : ℕ → Ω → G.Query → G.Reply
  sample_measurable : ∀ n,Measurable (fun z : Ω × G.Query => sample n z.1 z.2)
  obs_eq : ∀ n ω,obs n ω=sample n ω (A.program.query (state n ω))
  state_measurable : ∀ n,Measurable (state n)
  obs_measurable : ∀ n,Measurable (obs n)
  init : ∀ ω,state 0 ω=A.start (privateSeed ω)
  next : ∀ n ω,state (n+1) ω=if A.program.halt (state n ω)=true
    then state n ω else A.program.update (state n ω,obs n ω)
  information : ℕ → MeasurableSpace Ω
  information_le : ∀ n,information n≤measurableΩ
  information_mono : Monotone information
  obs_information : ∀ n,Measurable[information (n+1)] (obs n)
  query_information : ∀ n,Measurable[information n] (fun ω => A.program.query (state n ω))
  upper_square_integrable : ∀ n,Integrable (fun ω => ‖(obs n ω).1-M.upper (A.program.query (state n ω))‖^2) law
  lower_square_integrable : ∀ n,Integrable (fun ω => ‖(obs n ω).2-M.lower (A.program.query (state n ω))‖^2) law
  upper_mean : ∀ n,law[fun ω => (obs n ω).1-M.upper (A.program.query (state n ω)) | information n] =ᵐ[law] 0
  lower_mean : ∀ n,law[fun ω => (obs n ω).2-M.lower (A.program.query (state n ω)) | information n] =ᵐ[law] 0
  upper_variance : ∀ n,∀ᵐ ω ∂law,law[fun ω => ‖(obs n ω).1-M.upper (A.program.query (state n ω))‖^2 |
    information n] ω≤σf^2
  lower_variance : ∀ n,∀ᵐ ω ∂law,law[fun ω => ‖(obs n ω).2-M.lower (A.program.query (state n ω))‖^2 |
    information n] ω≤σg^2


attribute [instance] QuerySourceExecution.measurableΩ QuerySourceExecution.probability

namespace QuerySourceExecution
variable {G : Geometry} {M : SourceMean G μ L ρ Δ R₀} {A : Algorithm G}
variable (E : QuerySourceExecution M A σf σg)

def path (ω : E.Ω) : HistoryProgram.Path A.State Unit := fun n => (E.state n ω,())
theorem path_measurable : Measurable E.path :=
  measurable_pi_lambda _ (fun n => (E.state_measurable n).prodMk measurable_const)

def cost : ℝ≥0∞ := ∫⁻ ω,HistoryProgram.totalCalls A.program (E.path ω) ∂E.law

def risk : ℝ≥0∞ := ∫⁻ ω,ENNReal.ofReal (M.loss (HistoryProgram.stoppedOutput A.program (E.path ω))) ∂E.law

def IsConservative : Prop := ∀ n ω,∃ f g : G.Query → ℝ,
  (∀ q,HasGradientAt f (E.sample n ω q).1 q) ∧ (∀ q,HasGradientAt g (E.sample n ω q).2 q)

variable {P : PostAlgorithm G} (E : QuerySourceExecution M P.bodyAsAlgorithm σf σg)

def postOutput (z : P.Terminal × E.Ω) : G.X :=
  P.select (z.1,HistoryProgram.stoppedOutput P.packedBody (E.path z.2))

theorem postOutput_measurable : Measurable E.postOutput :=
  P.select_measurable.comp (measurable_fst.prodMk
    (((HistoryProgram.stoppedOutput_measurable P.packedBody).comp E.path_measurable).comp measurable_snd))

def postRisk : ℝ≥0∞ :=
  ∫⁻ z,ENNReal.ofReal (M.loss (E.postOutput z)) ∂P.terminalLaw.prod E.law

end QuerySourceExecution

/-- Mean constraints and conservative sample fields concern the same
actual query-adapted source execution. -/
structure QueryPostChallenge (A : PostSolverAt) (μ L ρ Δ R₀ σf σg : ℝ) where
  geometry : Geometry
  mean : SourceMean geometry μ L ρ Δ R₀
  execution : QuerySourceExecution mean (A geometry mean.x₀ mean.yinit).bodyAsAlgorithm σf σg

def queryPostAccurate (C : SourceMeanClass μ L ρ Δ R₀) (conservative : Bool)
    (ε : ℝ) (A : PostSolverAt) : Prop :=
  ∀ K : QueryPostChallenge A μ L ρ Δ R₀ σf σg,
    C K.geometry K.mean → (conservative=true → K.execution.IsConservative) → K.execution.postRisk≤ENNReal.ofReal ε

def queryPostWorstCost (C : SourceMeanClass μ L ρ Δ R₀) (conservative : Bool) (A : PostSolverAt) : ℝ≥0∞ :=
  ⨆ K : {K : QueryPostChallenge A μ L ρ Δ R₀ σf σg //
    C K.geometry K.mean ∧ (conservative=true → K.execution.IsConservative)},K.val.execution.cost

def queryPostComplexity (C : SourceMeanClass μ L ρ Δ R₀) (conservative : Bool) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ A : {A : PostSolverAt // queryPostAccurate (σf:=σf) (σg:=σg) C conservative ε A},
    queryPostWorstCost (σf:=σf) (σg:=σg) C conservative A.val

end Bilevel.PolishedHistory
