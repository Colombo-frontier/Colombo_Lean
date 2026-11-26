import Bilevel.HistoryProgramStopping
import Bilevel.PrimitiveQueryUpperSolver
import Bilevel.OracleCodeHistory

/-! The normalized primitive class with arbitrary history-dependent paired
conditional kernels. Algorithms are exactly the public measurable programs
used by `PrimitiveQuery`, not a restricted oracle-code syntax. The loss is
computed from the retained primitive; nontermination has infinite cost.

This definition uses the explicit Markov-kernel realization of conditional
SFO laws. Identifying all abstract conditional-expectation formulations with
such a realization is a distinct representation question. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery Stateful
set_option autoImplicit false

structure Instance (G : Geometry) (μ L ρ Δ R₀ σf σg : ℝ) where
  primitive : Model.Primitive (X:=G.X) (Y:=G.Y) μ L L L ρ
  response : primitive.Response
  x₀ : G.X
  yinit : G.Y
  gap : primitive.GapCertificate response x₀ Δ
  initialization : ‖yinit-response.y x₀‖ ≤ R₀
  History : Type
  [measurableHistory : MeasurableSpace History]
  initialHistory : History
  oracle : Stateful.HistorySFO (Query:=G.X × G.Y) (History:=History)
    (X:=G.X) (Y:=G.Y) σf σg
  truth_fx : ∀ x y,oracle.upper.truth_x (x,y)=primitive.fx x y
  truth_fy : ∀ x y,oracle.upper.truth_y (x,y)=primitive.fy x y
  truth_gx : ∀ x y,oracle.lower.truth_x (x,y)=primitive.gx x y
  truth_gy : ∀ x y,oracle.lower.truth_y (x,y)=primitive.gy x y

attribute [instance] Instance.measurableHistory

variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : Instance G μ L ρ Δ R₀ σf σg)

def Instance.rawRequest (z : G.Query × I.History) : (G.X × G.Y) × I.History :=
  (PrimitiveQuery.unpack z.1,z.2)

theorem Instance.rawRequest_measurable : Measurable I.rawRequest :=
  (PrimitiveQuery.unpack_measurable.comp measurable_fst).prodMk measurable_snd

/-- Coordinate conversion retains the same paired response and history. -/
def Instance.packedLaw : Kernel (G.Query × I.History) G.Reply :=
  (I.oracle.law.comap I.rawRequest I.rawRequest_measurable).map packResponse

instance Instance.packedLaw_markov : IsMarkovKernel I.packedLaw := by
  unfold Instance.packedLaw
  exact Kernel.IsMarkovKernel.map _ packResponse_measurable

theorem Instance.packedLaw_apply (q : G.Query) (h : I.History) :
    I.packedLaw (q,h)=(I.oracle.law (PrimitiveQuery.unpack q,h)).map packResponse := by
  rw [Instance.packedLaw,Kernel.map_apply _ packResponse_measurable,Kernel.comap_apply]
  rfl

def Instance.packedUpdate (z : (G.Query × I.History) × G.Reply) : I.History :=
  I.oracle.update (I.rawRequest z.1,splitResponse z.2)

theorem Instance.packedUpdate_measurable : Measurable I.packedUpdate :=
  I.oracle.update_measurable.comp ((I.rawRequest_measurable.comp measurable_fst).prodMk
    (splitResponse_measurable.comp measurable_snd))

def Instance.historyOracle : HistoryProgram.Oracle G.Query G.Reply I.History where
  law := I.packedLaw
  markov := inferInstance
  update := I.packedUpdate
  update_measurable := I.packedUpdate_measurable

/-- Actual Ionescu-Tulcea path law with an absorbing halting state. -/
def Instance.execution (A : Algorithm G) : Measure (HistoryProgram.Path A.State I.History) :=
  HistoryProgram.trajectoryLaw A.program I.historyOracle A.privateLaw A.start I.initialHistory

instance Instance.execution_probability (A : Algorithm G) :
    IsProbabilityMeasure (I.execution A) :=
  HistoryProgram.trajectoryLaw_probability A.program I.historyOracle A.privateLaw A.start
    A.start_measurable I.initialHistory

def Instance.loss (x : G.X) : ℝ := ‖gradient (I.primitive.hyperobjective I.response) x‖

theorem Instance.loss_measurable : Measurable I.loss :=
  (I.primitive.gradient_hyperobjective_lipschitz I.response).continuous.measurable.norm

def Instance.cost (A : Algorithm G) : ℝ≥0∞ :=
  ∫⁻ w,HistoryProgram.totalCalls A.program w ∂I.execution A

def Instance.risk (A : Algorithm G) : ℝ≥0∞ :=
  ∫⁻ w,ENNReal.ofReal (I.loss (HistoryProgram.stoppedOutput A.program w)) ∂I.execution A

theorem Instance.ae_terminated_of_cost_finite (A : Algorithm G) (hc : I.cost A ≠ ⊤) :
    ∀ᵐ w ∂I.execution A,HistoryProgram.Terminated A.program w :=
  HistoryProgram.ae_terminated_of_cost_finite A.program (I.execution A) hc

/-- A conservative sample is a global scalar gradient field; its law may
depend on the preceding history and its two vectors may be correlated. -/
structure ConservativeRealization where
  Seed : Type
  [measurableSeed : MeasurableSpace Seed]
  law : Kernel (G.Query × I.History) Seed
  markov : IsMarkovKernel law
  sample : I.History → G.Query → Seed → G.Reply
  sample_measurable : Measurable (fun z : I.History × G.Query × Seed =>
    sample z.1 z.2.1 z.2.2)
  law_eq : ∀ q h,I.packedLaw (q,h)=(law (q,h)).map (sample h q)
  potential : ∀ h c,∃ f g : G.Query → ℝ,
    (∀ q,HasGradientAt f (sample h q c).1 q) ∧
    (∀ q,HasGradientAt g (sample h q c).2 q)

attribute [instance] ConservativeRealization.measurableSeed ConservativeRealization.markov

def Instance.IsConservative : Prop := Nonempty (ConservativeRealization I)

def Instance.CurvatureBound (Λ : ℝ) : Prop :=
  ∀ x x',‖gradient (I.primitive.hyperobjective I.response) x-
    gradient (I.primitive.hyperobjective I.response) x'‖ ≤ Λ*‖x-x'‖

abbrev InstanceClass (μ L ρ Δ R₀ σf σg : ℝ) :=
  (G : Geometry) → Instance G μ L ρ Δ R₀ σf σg → Prop

/-- The supplied initialization is public input to one common solver. -/
abbrev SolverAt := (G : Geometry) → G.X → G.Y → Algorithm G

def Accurate (C : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ) (A : SolverAt) : Prop :=
  ∀ G (I : Instance G μ L ρ Δ R₀ σf σg),C G I →
    I.risk (A G I.x₀ I.yinit)≤ENNReal.ofReal ε

def Complexity (C : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ) : ℝ≥0∞ :=
  ChiMinimax.complexity
    (fun (A : SolverAt) (I : {I : (G : Geometry) × Instance G μ L ρ Δ R₀ σf σg // C I.1 I.2}) =>
      I.val.2.cost (A I.val.1 I.val.2.x₀ I.val.2.yinit)) (Accurate C ε)

def unrestrictedClass : InstanceClass μ L ρ Δ R₀ σf σg := fun _ _ => True

def conservativeClass : InstanceClass μ L ρ Δ R₀ σf σg := fun _ I => I.IsConservative

def curvatureClass (Λ : ℝ) : InstanceClass μ L ρ Δ R₀ σf σg := fun _ I => I.CurvatureBound Λ

def conservativeCurvatureClass (Λ : ℝ) : InstanceClass μ L ρ Δ R₀ σf σg :=
  fun _ I => I.IsConservative ∧ I.CurvatureBound Λ

end Bilevel.PolishedHistory
