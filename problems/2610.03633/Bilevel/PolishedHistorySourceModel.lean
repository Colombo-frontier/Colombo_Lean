import Bilevel.PolishedHistorySourceOneWay

/-! A direct source-probability model. Challenges are actual random-initial
conditional-moment executions, and costs/risks are computed from their
actual stopping paths. The fresh challenge is constructed, not assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery PrimitiveGeometry BorelAdaptive
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {μ L ρ Δ R₀ σf σg : ℝ}

structure SourceMean (G : Geometry) (μ L ρ Δ R₀ : ℝ) where
  primitive : Model.Primitive (X:=G.X) (Y:=G.Y) μ L L L ρ
  response : primitive.Response
  x₀ : G.X
  yinit : G.Y
  gap : primitive.GapCertificate response x₀ Δ
  initialization : ‖yinit-response.y x₀‖≤R₀

def SourceMean.upper {G : Geometry} (M : SourceMean G μ L ρ Δ R₀) (q : G.Query) : G.Query :=
  pack (M.primitive.fx q.fst q.snd) (M.primitive.fy q.fst q.snd)

def SourceMean.lower {G : Geometry} (M : SourceMean G μ L ρ Δ R₀) (q : G.Query) : G.Query :=
  pack (M.primitive.gx q.fst q.snd) (M.primitive.gy q.fst q.snd)

def SourceMean.loss {G : Geometry} (M : SourceMean G μ L ρ Δ R₀) (x : G.X) : ℝ :=
  ‖gradient (M.primitive.hyperobjective M.response) x‖

/-- The source oracle conditions on an actual probability space. Private
initial randomness has the algorithm's prescribed marginal. Each call has
one paired scalar-field draw; it may correlate the two returned vectors. -/
structure SourceRandomExecution {G : Geometry} (M : SourceMean G μ L ρ Δ R₀)
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
  init : ∀ᵐ ω ∂law,state 0 ω=A.start (privateSeed ω)
  next : ∀ n,∀ᵐ ω ∂law,state (n+1) ω=if A.program.halt (state n ω)=true
    then state n ω else A.program.update (state n ω,obs n ω)
  information : ℕ → MeasurableSpace Ω
  information_le : ∀ n,information n≤measurableΩ
  information_mono : Monotone information
  obs_information : ∀ n,Measurable[information (n+1)] (obs n)
  private_information : ∀ n,Measurable[information n] privateSeed
  state_information : ∀ n,Measurable[information n] (state n)
  upper_square_integrable : ∀ n,Integrable (fun ω => ‖(obs n ω).1-M.upper (A.program.query (state n ω))‖^2) law
  lower_square_integrable : ∀ n,Integrable (fun ω => ‖(obs n ω).2-M.lower (A.program.query (state n ω))‖^2) law
  upper_mean : ∀ n,law[fun ω => (obs n ω).1-M.upper (A.program.query (state n ω)) | information n] =ᵐ[law] 0
  lower_mean : ∀ n,law[fun ω => (obs n ω).2-M.lower (A.program.query (state n ω)) | information n] =ᵐ[law] 0
  upper_variance : ∀ n,∀ᵐ ω ∂law,law[fun ω => ‖(obs n ω).1-M.upper (A.program.query (state n ω))‖^2 |
    information n] ω≤σf^2
  lower_variance : ∀ n,∀ᵐ ω ∂law,law[fun ω => ‖(obs n ω).2-M.lower (A.program.query (state n ω))‖^2 |
    information n] ω≤σg^2

attribute [instance] SourceRandomExecution.measurableΩ SourceRandomExecution.probability

namespace SourceRandomExecution
variable {G : Geometry} {M : SourceMean G μ L ρ Δ R₀} {A : Algorithm G}
variable (E : SourceRandomExecution M A σf σg)

def path (ω : E.Ω) : HistoryProgram.Path A.State Unit := fun n => (E.state n ω,())
def cost : ℝ≥0∞ := ∫⁻ ω,HistoryProgram.totalCalls A.program (E.path ω) ∂E.law
def risk : ℝ≥0∞ := ∫⁻ ω,ENNReal.ofReal (M.loss (HistoryProgram.stoppedOutput A.program (E.path ω))) ∂E.law

def IsConservative : Prop := ∀ n ω,∃ f g : G.Query → ℝ,
  (∀ q,HasGradientAt f (E.sample n ω q).1 q) ∧ (∀ q,HasGradientAt g (E.sample n ω q).2 q)
end SourceRandomExecution

variable {G : Geometry} (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg)

def stationarySourceMean : SourceMean G μ L ρ Δ R₀ where
  primitive:=I.primitive
  response:=I.response
  x₀:=0
  yinit:=0
  gap:=I.gap
  initialization:=by simpa only [zero_sub,norm_neg] using I.initialization

/-- No representation axiom: this actual source execution is built from
the independent stream, and every conditional-moment field has a proof. -/
def stationarySourceExecution (A : Algorithm G) :
    SourceRandomExecution (stationarySourceMean I) A σf σg where
  Ω:=FreshSourceSpace I A
  law:=freshSourceLaw I A
  privateSeed:=Prod.fst
  private_measurable:=measurable_fst
  private_law:=by simp only [freshSourceLaw,Measure.map_fst_prod,measure_univ,one_smul]
  state:=freshSourceState I A
  obs:=freshSourceObservation I A
  sample:=fun n z q => I.reply () q (z.2 n)
  sample_measurable:=by
    intro n
    have hm : Measurable (fun z : FreshSourceSpace I A × G.Query => ((),(z.2,z.1.2 n))) :=
      measurable_const.prodMk (measurable_snd.prodMk
        ((measurable_pi_apply n).comp (measurable_snd.comp measurable_fst)))
    exact I.reply_measurable.comp hm
  obs_eq:=fun _ _ => rfl
  state_measurable:=freshSourceState_measurable I A
  obs_measurable:=freshSourceObservation_measurable I A
  init:=Filter.Eventually.of_forall (freshSourceState_initial I A)
  next:=fun n => Filter.Eventually.of_forall (freshSourceState_next I A n)
  information:=freshSourceInformation I A
  information_le:=freshSourceInformation_le I A
  information_mono:=freshSourceInformation_mono I A
  obs_information:=freshSourceObservation_information I A
  private_information:=fun n => (measurable_fst : Measurable (Prod.fst : A.Private × (Fin n → I.Seed) → A.Private)).comp
    (show Measurable[freshSourceInformation I A n] (freshSourcePast I A n) from Measurable.of_comap_le le_rfl)
  state_information:=freshSourceState_information I A
  upper_square_integrable:=by
    intro n
    have h := (freshSourceOracle_moments I A I.upper n).1
    simpa only [freshSource_upper_error,SourceMean.upper,stationarySourceMean] using h
  lower_square_integrable:=by
    intro n
    have h := (freshSourceOracle_moments I A I.lower n).1
    simpa only [freshSource_lower_error,SourceMean.lower,stationarySourceMean] using h
  upper_mean:=by
    intro n
    have h := (freshSourceOracle_moments I A I.upper n).2.1
    rw [funext (freshSource_upper_error I A n)] at h
    simpa only [SourceMean.upper,stationarySourceMean] using h
  lower_mean:=by
    intro n
    have h := (freshSourceOracle_moments I A I.lower n).2.1
    rw [funext (freshSource_lower_error I A n)] at h
    simpa only [SourceMean.lower,stationarySourceMean] using h
  upper_variance:=by
    intro n
    have h := (freshSourceOracle_moments I A I.upper n).2.2
    simpa only [freshSource_upper_error,SourceMean.upper,stationarySourceMean] using h
  lower_variance:=by
    intro n
    have h := (freshSourceOracle_moments I A I.lower n).2.2
    simpa only [freshSource_lower_error,SourceMean.lower,stationarySourceMean] using h

theorem stationarySourceExecution_cost (A : Algorithm G) : (stationarySourceExecution I A).cost=I.cost A := rfl
theorem stationarySourceExecution_risk (A : Algorithm G) : (stationarySourceExecution I A).risk=I.risk A := rfl

theorem stationarySourceExecution_conservative (A : Algorithm G) (hI : I.IsConservative) :
    (stationarySourceExecution I A).IsConservative := fun n z => hI (z.2 n)

/-- A source challenge contains an actual primitive and an actual legal
execution of the selected randomized algorithm. The adversarial supremum
is taken after that algorithm has been fixed. -/
structure SourceChallenge (A : SolverAt) (μ L ρ Δ R₀ σf σg : ℝ) where
  geometry : Geometry
  mean : SourceMean geometry μ L ρ Δ R₀
  execution : SourceRandomExecution mean (A geometry mean.x₀ mean.yinit) σf σg

def sourceChallengeAccurate (conservative : Bool) (ε : ℝ) (A : SolverAt) : Prop :=
  ∀ C : SourceChallenge A μ L ρ Δ R₀ σf σg,
    (conservative=true → C.execution.IsConservative) → C.execution.risk≤ENNReal.ofReal ε

def sourceChallengeWorstCost (conservative : Bool) (A : SolverAt) : ℝ≥0∞ :=
  ⨆ C : {C : SourceChallenge A μ L ρ Δ R₀ σf σg // conservative=true → C.execution.IsConservative},C.val.execution.cost

def sourceChallengeComplexity (conservative : Bool) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ A : {A : SolverAt // sourceChallengeAccurate (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) conservative ε A},
    sourceChallengeWorstCost (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) conservative A.val

/-- Canonical hard source challenge for any fixed algorithm; neither its
moments nor its costs/risks are supplied as assumptions. -/
def stationarySourceChallenge (A : SolverAt) : SourceChallenge A μ L ρ Δ R₀ σf σg where
  geometry:=G
  mean:=stationarySourceMean I
  execution:=stationarySourceExecution I (A G 0 0)

/-- Actual source class inclusion and minimax order, with no embedding
parameter. Both unrestricted and globally conservative executions apply. -/
theorem stationary_minimax_le_actual_source (conservative : Bool) (ε : ℝ) :
    PrimitiveQuery.Complexity (PrimitiveQuery.conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε≤
      sourceChallengeComplexity (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) conservative ε := by
  unfold sourceChallengeComplexity PrimitiveQuery.Complexity ChiMinimax.complexity
  apply le_iInf
  intro A
  let oldSolver : PrimitiveQuery.Solver := fun G => A.val G 0 0
  have hacc : PrimitiveQuery.Accurate (PrimitiveQuery.conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε oldSolver := by
    intro G I hI
    have h := A.property (stationarySourceChallenge I A.val) (fun _ => stationarySourceExecution_conservative I (A.val G 0 0) hI)
    exact h
  refine (iInf_le _ ⟨oldSolver,hacc⟩).trans ?_
  apply iSup_le
  intro I
  exact le_iSup_of_le ⟨stationarySourceChallenge I.val.2 A.val,
    fun _ => stationarySourceExecution_conservative I.val.2 (A.val I.val.1 0 0) I.property⟩ le_rfl

/-- Original source-wide lower bound over actual conditional probability
experiments. There is no FreshSourceEmbedding or complexity-bound premise. -/
theorem uniform_actual_source_classes_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ^2 → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      ∀ conservative : Bool,
      ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        sourceChallengeComplexity (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) conservative ε := by
  obtain ⟨c,cq,hc,hc1,hcq,q,hl⟩ := ChiUniformLower.uniform_both_classes_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc conservative
  exact (hl L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc).1.trans
    (stationary_minimax_le_actual_source conservative ε)

end Bilevel.PolishedHistory
