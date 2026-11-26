import VIReference.Pilot.AdmissibleOracle
import VIReference.Pilot.BorelRunner
import VIReference.Pilot.LowerBudgetClosure

/-!
# Operational complexity in the Borel stopping-policy model

This file states deterministic and randomized success in the same measurable,
genuinely early-stopping policy type.  It supplies the direct singleton-seed
promotion behind `T_rand ≤ T_det` and abstract adapters by which lower-bound
failure witnesses rule out a surviving budget.
-/

open Set MeasureTheory
open scoped ENNReal

namespace VIReference.Pilot

noncomputable section

universe u v

section FeasibleRunner

variable {E : Type u} {Answer : Type v}
  [MeasurableSpace E] [MeasurableSpace Answer]
  {X : Set E} {budget : ℕ}

/-- Extend an oracle defined only on legal query points to the ambient space.
The fallback branch is operationally unreachable because every policy query
has subtype `X`. -/
def BorelStoppingPolicy.feasibleOracleExtension
    (oracle : X → Answer) (dummy : Answer) : E → Answer :=
  by
    classical
    exact fun x => if hx : x ∈ X then oracle ⟨x, hx⟩ else dummy

@[simp] theorem BorelStoppingPolicy.feasibleOracleExtension_apply
    (oracle : X → Answer) (dummy : Answer) (point : X) :
    BorelStoppingPolicy.feasibleOracleExtension oracle dummy point.1 = oracle point := by
  simp [BorelStoppingPolicy.feasibleOracleExtension, point.2]

/-- Execute a Borel stopping policy against an oracle available on exactly the
feasible domain.  The singleton `Unit` below is only the runner's external
environment; the policy retains its own (possibly randomized) seed. -/
def BorelStoppingPolicy.runFeasibleOracle
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (oracle : X → Answer) (fill : X) (dummy : Answer)
    (seed : policy.Seed) : X :=
  BorelStoppingPolicy.runnerOutput policy
    (fun (_ : Unit) (_ : Fin budget) =>
      BorelStoppingPolicy.feasibleOracleExtension oracle dummy)
    fill dummy ((), seed)

/-- The preceding executable output is backed by a genuine unpadded run with
at most the declared budget. -/
theorem BorelStoppingPolicy.runFeasibleOracle_executes
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (oracle : X → Answer) (fill : X) (dummy : Answer)
    (seed : policy.Seed) :
    ∃ n, ∃ hn : n ≤ budget, ∃ history : OracleHistory X Answer n,
      policy.IsUnpaddedRun (BorelStoppingPolicy.feasibleOracleExtension oracle dummy)
        seed n hn history (policy.runFeasibleOracle oracle fill dummy seed) := by
  let stageOracle := fun (_ : Unit) (_ : Fin budget) =>
    BorelStoppingPolicy.feasibleOracleExtension oracle dummy
  obtain ⟨n, hn, _hcount, hrun⟩ :=
    BorelStoppingPolicy.runner_executes_fixedOracle_of_coupled
      policy stageOracle
        (fun _ : Unit => BorelStoppingPolicy.feasibleOracleExtension oracle dummy)
      fill dummy ((), seed) (fun _ _ => rfl)
  exact ⟨n, hn, _, hrun⟩

end FeasibleRunner

section ExactComplexity

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Canonical zero element of the ambient symmetric jet space. -/
def zeroSymmetricExactJet (p : ℕ) : SymmetricExactJet E p :=
  fun _ => ⟨0, fun _ => rfl⟩

/-- Operational output of the fixed Borel policy against the canonical exact
feasible oracle supplied by admissibility. -/
def admissibleBorelOutput (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) (budget : ℕ)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E data.p) data.X budget)
    (seed : policy.Seed) : data.X :=
  policy.runFeasibleOracle
    (hF.feasibleExactSymmetricJetOracle data F).answer
    ⟨data.x0, data.x0_mem⟩ (zeroSymmetricExactJet data.p) seed

/-- Uniform deterministic success inside the Borel policy model.  Determinism
means an inhabited subsingleton seed, and success is pointwise in that unique
seed for every admissible operator. -/
def BorelDeterministicUniformSuccess (data : VIPublicData E) (budget : ℕ)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E data.p) data.X budget)
    (epsilon : ℝ) : Prop :=
  policy.IsDeterministic ∧
  ∀ (F : E → E) (hF : IsAdmissibleOperator data F) (seed : policy.Seed),
    tangentResidual data F (admissibleBorelOutput data F hF budget policy seed).1 ≤ epsilon

/-- Uniform randomized success, with a measurable success event of probability
at least `2/3`, for every admissible operator. -/
def BorelRandomUniformSuccess (data : VIPublicData E) (budget : ℕ)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E data.p) data.X budget)
    (epsilon : ℝ) : Prop :=
  ∀ (F : E → E) (hF : IsAdmissibleOperator data F),
    @MeasurableSet policy.Seed policy.seedMeasurable
      {seed | tangentResidual data F
        (admissibleBorelOutput data F hF budget policy seed).1 ≤ epsilon} ∧
    (2 / 3 : ℝ≥0∞) ≤ policy.seedMeasure
      {seed | tangentResidual data F
        (admissibleBorelOutput data F hF budget policy seed).1 ≤ epsilon}

/-- Pointwise singleton-seed success promotes the very same Borel policy to
randomized success; there is no conversion through an older policy syntax. -/
theorem borelDeterministicUniformSuccess_to_random
    (data : VIPublicData E) (budget : ℕ)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E data.p) data.X budget)
    (epsilon : ℝ)
    (hsuccess : BorelDeterministicUniformSuccess data budget policy epsilon) :
    BorelRandomUniformSuccess data budget policy epsilon := by
  intro F hF
  letI : MeasurableSpace policy.Seed := policy.seedMeasurable
  letI : IsProbabilityMeasure policy.seedMeasure := policy.seedProbability
  have hevent :
      {seed : policy.Seed | tangentResidual data F
        (admissibleBorelOutput data F hF budget policy seed).1 ≤ epsilon} = Set.univ := by
    ext seed
    simp [hsuccess.2 F hF seed]
  constructor
  · rw [hevent]
    exact MeasurableSet.univ
  · rw [hevent, measure_univ]
    calc
      (2 / 3 : ℝ≥0∞) ≤ 3 / 3 :=
        ENNReal.div_le_div_right (by norm_num : (2 : ℝ≥0∞) ≤ 3) 3
      _ = 1 := ENNReal.div_self (by norm_num) (by norm_num)

/-- A deterministic budget survives if one deterministic Borel policy of that
budget succeeds uniformly. -/
def BorelDeterministicBudgetSurvives
    (data : VIPublicData E) (budget : ℕ) (epsilon : ℝ) : Prop :=
  ∃ policy : BorelStoppingPolicy.{u, u, 0}
      (Answer := SymmetricExactJet E data.p) data.X budget,
    BorelDeterministicUniformSuccess data budget policy epsilon

/-- A randomized budget survives if one Borel policy of that budget succeeds
uniformly with probability at least `2/3`. -/
def BorelRandomBudgetSurvives
    (data : VIPublicData E) (budget : ℕ) (epsilon : ℝ) : Prop :=
  ∃ policy : BorelStoppingPolicy.{u, u, 0}
      (Answer := SymmetricExactJet E data.p) data.X budget,
    BorelRandomUniformSuccess data budget policy epsilon

/-- Direct operational form of `T_rand ≤ T_det` in one policy model. -/
theorem borelRandomBudgetSurvives_of_deterministic
    (data : VIPublicData E) (budget : ℕ) (epsilon : ℝ) :
    BorelDeterministicBudgetSurvives data budget epsilon →
      BorelRandomBudgetSurvives data budget epsilon := by
  rintro ⟨policy, hpolicy⟩
  exact ⟨policy,
    borelDeterministicUniformSuccess_to_random data budget policy epsilon hpolicy⟩

/-- A source-facing relation between the two operational query complexities:
every deterministic surviving cap is also a randomized surviving cap. -/
def BorelRandomizedLeDeterministicClaim : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (data : VIPublicData E) (budget : ℕ) (epsilon : ℝ),
    BorelDeterministicBudgetSurvives data budget epsilon →
      BorelRandomBudgetSurvives data budget epsilon

theorem borelRandomizedLeDeterministicClaim_proof :
    BorelRandomizedLeDeterministicClaim := by
  intro E _ _ _ _ _ data budget epsilon
  exact borelRandomBudgetSurvives_of_deterministic data budget epsilon

end ExactComplexity

section LowerAdapters

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A lower-bound failure witness for a fixed Borel policy: on one admissible
operator, a measurable set of seeds of mass strictly above `1/3` misses the
target residual. -/
def BorelUniformFailureWitness (data : VIPublicData E) (budget : ℕ)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E data.p) data.X budget)
    (epsilon : ℝ) : Prop :=
  ∃ (F : E → E) (hF : IsAdmissibleOperator data F),
    @MeasurableSet policy.Seed policy.seedMeasurable
      {seed | epsilon < tangentResidual data F
        (admissibleBorelOutput data F hF budget policy seed).1} ∧
    (1 / 3 : ℝ≥0∞) < policy.seedMeasure
      {seed | epsilon < tangentResidual data F
        (admissibleBorelOutput data F hF budget policy seed).1}

/-- Any `>1/3` failure witness contradicts uniform `2/3` success for the same
policy and the same operational runner. -/
theorem BorelUniformFailureWitness.not_randomUniformSuccess
    (data : VIPublicData E) (budget : ℕ)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E data.p) data.X budget)
    (epsilon : ℝ)
    (hfail : BorelUniformFailureWitness data budget policy epsilon) :
    ¬ BorelRandomUniformSuccess data budget policy epsilon := by
  intro hsuccess
  letI : MeasurableSpace policy.Seed := policy.seedMeasurable
  letI : IsProbabilityMeasure policy.seedMeasure := policy.seedProbability
  obtain ⟨F, hF, hfailMeas, hfailMass⟩ := hfail
  obtain ⟨hsuccessMeas, hsuccessMass⟩ := hsuccess F hF
  let success : Set policy.Seed := {seed | tangentResidual data F
    (admissibleBorelOutput data F hF budget policy seed).1 ≤ epsilon}
  let failure : Set policy.Seed := {seed | epsilon < tangentResidual data F
    (admissibleBorelOutput data F hF budget policy seed).1}
  have hdisjoint : Disjoint success failure := by
    rw [Set.disjoint_left]
    intro seed hs hf
    change tangentResidual data F
      (admissibleBorelOutput data F hF budget policy seed).1 ≤ epsilon at hs
    change epsilon < tangentResidual data F
      (admissibleBorelOutput data F hF budget policy seed).1 at hf
    exact (not_lt_of_ge hs) hf
  change MeasurableSet success at hsuccessMeas
  change MeasurableSet failure at hfailMeas
  have hunion : policy.seedMeasure (success ∪ failure) =
      policy.seedMeasure success + policy.seedMeasure failure :=
    measure_union hdisjoint hfailMeas
  have hle : policy.seedMeasure success + policy.seedMeasure failure ≤ 1 := by
    rw [← hunion]
    calc
      policy.seedMeasure (success ∪ failure) ≤ policy.seedMeasure Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  have hgt : 1 < policy.seedMeasure success + policy.seedMeasure failure := by
    have hthirds : (1 : ℝ≥0∞) = (2 / 3 : ℝ≥0∞) + 1 / 3 := by
      apply le_antisymm
      · apply (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mp
        rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
        simp only [ENNReal.toReal_div]
        norm_num
      · apply (ENNReal.toReal_le_toReal (by finiteness) (by simp)).mp
        rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
        simp only [ENNReal.toReal_div]
        norm_num
    calc
      1 = (2 / 3 : ℝ≥0∞) + 1 / 3 := hthirds
      _ < policy.seedMeasure success + policy.seedMeasure failure :=
        ENNReal.add_lt_add_of_le_of_lt (by finiteness) hsuccessMass hfailMass
  exact (not_lt_of_ge hle) hgt

/-- A budget-wide lower obstruction is exactly a failure witness for every
candidate Borel policy at that cap. -/
def BorelBudgetFailureObstruction
    (data : VIPublicData E) (budget : ℕ) (epsilon : ℝ) : Prop :=
  ∀ policy : BorelStoppingPolicy.{u, u, 0}
      (Answer := SymmetricExactJet E data.p) data.X budget,
    BorelUniformFailureWitness data budget policy epsilon

/-- Adapter used by positive-budget random lower bounds: a budget-wide
failure obstruction rules out randomized survival. -/
theorem not_borelRandomBudgetSurvives_of_failureObstruction
    (data : VIPublicData E) (budget : ℕ) (epsilon : ℝ)
    (hobstruction : BorelBudgetFailureObstruction data budget epsilon) :
    ¬ BorelRandomBudgetSurvives data budget epsilon := by
  rintro ⟨policy, hsuccess⟩
  exact (hobstruction policy).not_randomUniformSuccess data budget policy epsilon hsuccess

end LowerAdapters

end

end VIReference.Pilot
