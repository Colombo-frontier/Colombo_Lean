import Mathlib

/-!
# Public VI data, admissible operators, and exact adaptive oracle policies

This file formalizes the semantic core of LaTeX claims `def:class` and
`def:policy`.  The public problem is separated from the unknown operator, so a
policy cannot depend on `F`; uniform success quantifies over `F` only after the
policy has been fixed.
-/

open scoped ENNReal NNReal RealInnerProductSpace
open Set MeasureTheory

namespace VIReference.Pilot

section VIModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Public data for the monotone variational inequality. -/
structure VIPublicData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] where
  dimension_pos : 0 < Module.finrank ℝ E
  p : ℕ
  p_ge_two : 2 ≤ p
  Lp : ℝ
  Lp_pos : 0 < Lp
  D : ℝ
  D_pos : 0 < D
  X : Set E
  X_nonempty : X.Nonempty
  X_compact : IsCompact X
  X_convex : Convex ℝ X
  x0 : E
  x0_mem : x0 ∈ X
  diameter_le : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ D

/-- The operator class in `def:class`, with the top derivative represented by
mathlib's iterated Fréchet derivative. -/
structure IsAdmissibleOperator (data : VIPublicData E) (F : E → E) : Prop where
  regularity : ∃ U : Set E,
    IsOpen U ∧ data.X ⊆ U ∧ ContDiffOn ℝ (data.p - 1) F U
  monotone_on : (x : E) → x ∈ data.X → (y : E) → y ∈ data.X →
    0 ≤ inner ℝ (F x - F y) (x - y)
  top_derivative_lipschitz : (x : E) → x ∈ data.X → (y : E) → y ∈ data.X →
    ‖iteratedFDeriv ℝ (data.p - 1) F x -
        iteratedFDeriv ℝ (data.p - 1) F y‖ ≤ data.Lp * ‖x - y‖

/-- The VI solution predicate appearing in `def:class`. -/
def IsVISolution (data : VIPublicData E) (F : E → E) (xStar : E) : Prop :=
  xStar ∈ data.X ∧ ∀ x ∈ data.X, 0 ≤ inner ℝ (F xStar) (x - xStar)

/-- Outward normal cone, with the sign convention used by the article. -/
def normalCone (X : Set E) (x : E) : Set E :=
  {n | ∀ z ∈ X, inner ℝ n (z - x) ≤ 0}

/-- Same-point tangent residual `dist(0, F(x) + N_X(x))`. -/
noncomputable def tangentResidual (data : VIPublicData E) (F : E → E) (x : E) : ℝ :=
  Metric.infDist 0 ((fun n => F x + n) '' normalCone data.X x)

/-- A complete order-`p` jet.  Index `j : Fin p` stores the `j`th iterated
Fréchet derivative, including `j = 0` (the value of `F`). -/
abbrev ExactJet (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : ℕ) := (j : Fin p) → E [×j.1]→L[ℝ] E

/-- The exact jet returned at a feasible query. -/
noncomputable def exactJet (p : ℕ) (F : E → E) (x : E) : ExactJet E p :=
  fun j => iteratedFDeriv ℝ j.1 F x

end VIModel

section Policy

variable {E : Type*}

/-- A total deterministic adaptive strategy with at most `budget` queries.
Every query and every leaf output is feasible.  A leaf output need not be one
of the queried points. -/
inductive DeterministicPolicy (X : Set E) (Answer : Type*) : ℕ → Type _ where
  | done {budget : ℕ} : X → DeterministicPolicy X Answer budget
  | query {budget : ℕ} : X → (Answer → DeterministicPolicy X Answer budget) →
      DeterministicPolicy X Answer (budget + 1)

namespace DeterministicPolicy

/-- Execute a strategy tree against an oracle.  Structural recursion makes the
query cap part of the type. -/
def run {X : Set E} {Answer : Type*} (oracle : E → Answer) :
    {budget : ℕ} → DeterministicPolicy X Answer budget → X
  | _, .done output => output
  | _, @DeterministicPolicy.query _ _ _ _ queryPoint next =>
      run oracle (next (oracle queryPoint.1))

end DeterministicPolicy

end Policy

section BorelPolicy

variable {E Answer : Type*} [MeasurableSpace E] [MeasurableSpace Answer]

/-- The length-`n` history used in `def:policy`.  Each entry contains a
feasible query and the exact oracle answer returned at that query. -/
abbrev OracleHistory (X : Set E) (Answer : Type*) (n : ℕ) :=
  Fin n → X × Answer

/-- Exact fixed-cap randomized policy interface from `def:policy`.

The seed space and its probability law are fields of the policy, while the
unknown operator is not.  Consequently a value of this type is fixed before
the later universal quantifier over operators.  Rules are total and Borel
measurable, every query/output has subtype `X`, and the final output is an
arbitrary feasible point rather than a previously queried point.

This fixed-history shell models the Borel part of a policy that reaches its
cap.  Exact measurable early stopping is represented structurally by
`DeterministicPolicy`; combining both views without padded oracle calls remains
an explicit pilot obligation.
-/
structure BorelOraclePolicy (X : Set E) (budget : ℕ) where
  Seed : Type*
  seedMeasurable : MeasurableSpace Seed
  seedMeasure : @MeasureTheory.Measure Seed seedMeasurable
  seedProbability : @IsProbabilityMeasure Seed seedMeasurable seedMeasure
  queryRule : (n : Fin budget) → Seed × OracleHistory X Answer n.1 → X
  queryRule_measurable : ∀ n, @Measurable
    (Seed × OracleHistory X Answer n.1) X
    (MeasurableSpace.prod seedMeasurable inferInstance) inferInstance
    (queryRule n)
  outputRule : Seed × OracleHistory X Answer budget → X
  outputRule_measurable : @Measurable
    (Seed × OracleHistory X Answer budget) X
    (MeasurableSpace.prod seedMeasurable inferInstance) inferInstance
    outputRule

end BorelPolicy

section UniformQuantifiers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Uniform deterministic success: the policy is fixed from public data before
the unknown admissible operator is universally quantified. -/
def DeterministicUniformSuccess (data : VIPublicData E) (budget : ℕ)
    (policy : DeterministicPolicy data.X (ExactJet E data.p) budget)
    (ε : ℝ) : Prop :=
  ∀ F : E → E, IsAdmissibleOperator data F →
    tangentResidual data F
      (policy.run (exactJet data.p F) : E) ≤ ε

/-- A randomized method is a probability distribution over deterministic
adaptive policies.  Its seed and strategy family are fixed before `F` is
quantified, expressing independence of the random seed from the unknown
operator. -/
structure RandomizedPolicy (data : VIPublicData E) (budget : ℕ) where
  Seed : Type*
  seedMeasurable : MeasurableSpace Seed
  seedMeasure : @Measure Seed seedMeasurable
  seedProbability : seedMeasure Set.univ = 1
  choose : Seed → DeterministicPolicy data.X (ExactJet E data.p) budget

/-- Per-instance success probability at least `2/3`, uniformly for every
admissible operator compatible with the fixed public input. -/
def RandomizedUniformSuccess (data : VIPublicData E) (budget : ℕ)
    (policy : RandomizedPolicy data budget) (ε : ℝ) : Prop := by
  letI := policy.seedMeasurable
  exact ∀ F : E → E, IsAdmissibleOperator data F →
    MeasurableSet {ξ | tangentResidual data F
      ((policy.choose ξ).run (exactJet data.p F) : E) ≤ ε} ∧
    policy.seedMeasure {ξ | tangentResidual data F
      ((policy.choose ξ).run (exactJet data.p F) : E) ≤ ε} ≥ (2 / 3 : ℝ≥0∞)

end UniformQuantifiers

end VIReference.Pilot
