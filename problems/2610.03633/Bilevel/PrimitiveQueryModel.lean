import Bilevel.PrimitiveQueryGeometry
import Bilevel.FreshOracle
import Bilevel.IndependentStream
import Bilevel.BorelAdaptiveExtendedCalls
import Bilevel.ChiMinimaxAssembly

/-! An actual original-SFO minimax model. The solver receives public geometry,
not a hidden Primitive, its gradients, its oracle seed, or its sample law.
One transition consumes one paired full-gradient sample. Nontermination has
infinite cost, and the terminal point may be any measurable program output.
The fresh law may correlate the upper and lower observations within a call. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PrimitiveQuery
open PrimitiveGeometry BorelAdaptive
set_option autoImplicit false

structure Algorithm (G : Geometry) where
  Private : Type
  State : Type
  [measurablePrivate : MeasurableSpace Private]
  [measurableState : MeasurableSpace State]
  privateLaw : Measure Private
  [probability : IsProbabilityMeasure privateLaw]
  program : Program State G.Query G.Reply G.X
  start : Private → State
  start_measurable : Measurable start

attribute [instance] Algorithm.measurablePrivate Algorithm.measurableState Algorithm.probability

/-- Every dimension gets a program before the hidden mean instance is selected. -/
abbrev Solver := (G : Geometry) → Algorithm G

structure Instance (G : Geometry) (μ L ρ Δ R₀ σf σg : ℝ) where
  primitive : Model.Primitive (X:=G.X) (Y:=G.Y) μ L L L ρ
  response : primitive.Response
  gap : primitive.GapCertificate response 0 Δ
  initialization : ‖response.y 0‖ ≤ R₀
  Seed : Type
  [measurableSeed : MeasurableSpace Seed]
  law : Measure Seed
  [probability : IsProbabilityMeasure law]
  upper : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query) law σf
  lower : FreshOracle.Oracle (Query:=G.Query) (E:=G.Query) law σg
  upper_truth : ∀ q,upper.truth q=pack (primitive.fx q.fst q.snd) (primitive.fy q.fst q.snd)
  lower_truth : ∀ q,lower.truth q=pack (primitive.gx q.fst q.snd) (primitive.gy q.fst q.snd)

attribute [instance] Instance.measurableSeed Instance.probability

variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : Instance G μ L ρ Δ R₀ σf σg)

def Instance.reply (_ : Unit) (q : G.Query) (c : I.Seed) : G.Reply :=
  (I.upper.sample q c,I.lower.sample q c)

def Instance.loss (x : G.X) : ℝ := ‖gradient (I.primitive.hyperobjective I.response) x‖

/-- Globally defined scalar sample potentials, for every sample, not just a.e. -/
def Instance.IsConservative : Prop :=
  ∀ c : I.Seed,∃ f g : G.Query → ℝ,
    (∀ q,HasGradientAt f (I.upper.sample q c) q) ∧
    (∀ q,HasGradientAt g (I.lower.sample q c) q)

def Instance.CurvatureBound (Λ : ℝ) : Prop :=
  ∀ x x',‖gradient (I.primitive.hyperobjective I.response) x-
    gradient (I.primitive.hyperobjective I.response) x'‖ ≤ Λ*‖x-x'‖

def Instance.cost (A : Algorithm G) : ℝ≥0∞ :=
  ∫⁻ z,seededCalls A.program I.reply A.start ((),z)
    ∂A.privateLaw.prod (IndependentStream.law I.law)

def Instance.risk (A : Algorithm G) : ℝ≥0∞ :=
  ∫⁻ z,ENNReal.ofReal (I.loss (seededStopped A.program I.reply A.start ((),z)).2)
    ∂A.privateLaw.prod (IndependentStream.law I.law)

abbrev InstanceClass (μ L ρ Δ R₀ σf σg : ℝ) :=
  (G : Geometry) → Instance G μ L ρ Δ R₀ σf σg → Prop

def Accurate (C : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ) (A : Solver) : Prop :=
  ∀ G (I : Instance G μ L ρ Δ R₀ σf σg),C G I → I.risk (A G)≤ENNReal.ofReal ε

def Complexity (C : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ) : ℝ≥0∞ :=
  ChiMinimax.complexity
    (fun (A : Solver) (I : {I : (G : Geometry) × Instance G μ L ρ Δ R₀ σf σg // C I.1 I.2}) =>
      I.val.2.cost (A I.val.1)) (Accurate C ε)

def unrestrictedClass : InstanceClass μ L ρ Δ R₀ σf σg := fun _ _ => True
def conservativeClass : InstanceClass μ L ρ Δ R₀ σf σg := fun _ I => I.IsConservative
def curvatureClass (Λ : ℝ) : InstanceClass μ L ρ Δ R₀ σf σg := fun _ I => I.CurvatureBound Λ
def conservativeCurvatureClass (Λ : ℝ) : InstanceClass μ L ρ Δ R₀ σf σg :=
  fun _ I => I.IsConservative ∧ I.CurvatureBound Λ

theorem Instance.reply_measurable :
    Measurable (fun z : Unit × (G.Query × I.Seed) => I.reply z.1 z.2.1 z.2.2) :=
  (I.upper.sample_measurable.prodMk I.lower.sample_measurable).comp measurable_snd

theorem lower_of_hard_instance (C : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ) (R : ℝ≥0∞)
    (h : ∀ A : Solver,Accurate C ε A →
      ∃ (G : Geometry) (I : Instance G μ L ρ Δ R₀ σf σg),C G I ∧ R≤I.cost (A G)) :
    R≤Complexity C ε := by
  apply ChiMinimax.lower_of_hard_instance
  intro A hA
  obtain ⟨G,I,hI,hcost⟩ := h A hA
  exact ⟨⟨⟨G,I⟩,hI⟩,hcost⟩

end Bilevel.PrimitiveQuery
