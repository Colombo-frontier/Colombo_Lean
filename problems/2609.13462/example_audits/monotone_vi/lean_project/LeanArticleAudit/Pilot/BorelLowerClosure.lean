import LeanArticleAudit.Pilot.LowerBudgetClosure
import LeanArticleAudit.Pilot.UpperBorelComplexity

/-!
# Borel-policy lower-budget closure

This module connects the paper's concrete zero-query and random-frame
obstructions to *successful policies* in the single `BorelStoppingPolicy`
model.  In particular, the final lower inequality no longer uses the
auxiliary abbreviation “survives = not obstructed” as a proxy for existence
of an actual uniformly successful policy.
-/

open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace LeanArticleAudit.Pilot

noncomputable section

private theorem exact_feasible_answers_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (data : VIPublicData E) (F : E → E)
    (oracle₁ oracle₂ : FeasibleExactSymmetricJetOracle data F)
    (x : data.X) : oracle₁.answer x = oracle₂.answer x := by
  funext j
  apply Subtype.ext
  rw [oracle₁.exact, oracle₂.exact]

private theorem runnerState_const_environment_eq
    {E Answer Ω₁ Ω₂ : Type*}
    [MeasurableSpace E] [MeasurableSpace Answer]
    {X : Set E} {budget : ℕ}
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (oracle : Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (omega₁ : Ω₁) (omega₂ : Ω₂) (seed : policy.Seed)
    (n : ℕ) (hn : n ≤ budget) :
    BorelStoppingPolicy.runnerState policy (fun (_ : Ω₁) => oracle)
        fill dummy n hn (omega₁, seed) =
      BorelStoppingPolicy.runnerState policy (fun (_ : Ω₂) => oracle)
        fill dummy n hn (omega₂, seed) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [BorelStoppingPolicy.runnerState]
      rw [ih (by omega)]
      rfl

private theorem runnerOutput_const_environment_eq
    {E Answer Ω₁ Ω₂ : Type*}
    [MeasurableSpace E] [MeasurableSpace Answer]
    {X : Set E} {budget : ℕ}
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (oracle : Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (omega₁ : Ω₁) (omega₂ : Ω₂) (seed : policy.Seed) :
    BorelStoppingPolicy.runnerOutput policy (fun (_ : Ω₁) => oracle)
        fill dummy (omega₁, seed) =
      BorelStoppingPolicy.runnerOutput policy (fun (_ : Ω₂) => oracle)
        fill dummy (omega₂, seed) := by
  simp only [BorelStoppingPolicy.runnerOutput]
  rw [runnerState_const_environment_eq policy oracle fill dummy omega₁ omega₂
    seed budget le_rfl]

/-- The canonical hidden-operator runner used by the random lower bound and
the canonical feasible-oracle runner used by `BorelRandomUniformSuccess`
return the same point.  The fill point and dummy jet are chosen identically;
the dummy branch is unreachable because every query is feasible. -/
theorem actualHiddenRunnerOutput_eq_admissibleBorelOutput
    {d p N : ℕ} {R : ℝ} [NeZero d]
    (prior : SequentialFramePrior (EuclideanSpace ℝ (Fin d)) N d R)
    (hp : 2 ≤ p)
    (Lp : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) N)
    (omega : prior.Omega)
    (hF : IsAdmissibleOperator
      (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
      (hiddenOperator p standardGateProfile Lp R N (prior.frame omega)))
    (seed : policy.Seed) :
    let data := ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR
    let F := hiddenOperator p standardGateProfile Lp R N (prior.frame omega)
    actualHiddenRunnerOutput prior p hp standardGateProfile Lp hLp hR policy
        ⟨data.x0, data.x0_mem⟩ (zeroSymmetricExactJet p) omega seed =
      admissibleBorelOutput data F hF N policy seed := by
  dsimp [actualHiddenRunnerOutput, admissibleBorelOutput,
    BorelStoppingPolicy.runFeasibleOracle]
  calc
    _ = BorelStoppingPolicy.runnerOutput policy
        (fun (_omega : prior.Omega) (_t : Fin N) =>
          BorelStoppingPolicy.feasibleOracleExtension
            (hF.feasibleExactSymmetricJetOracle
              (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
              (hiddenOperator p standardGateProfile Lp R N
                (prior.frame omega))).answer
            (zeroSymmetricExactJet p))
        ⟨(ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR).x0,
          (ballVIData p hp Lp hLp R hR).x0_mem⟩
        (zeroSymmetricExactJet p) (omega, seed) := by
      apply BorelStoppingPolicy.runnerOutput_eq_of_answerAtRunnerQuery
      intro t
      let q := policy.runnerQuery
        (fun omega (_t : Fin N) x =>
          (finalHiddenExactOracle p hp standardGateProfile Lp hLp R hR N
            (prior.frame omega)).answer x)
        ⟨(ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR).x0,
          (ballVIData p hp Lp hLp R hR).x0_mem⟩
        (zeroSymmetricExactJet p) t (omega, seed)
      change (finalHiddenExactOracle p hp standardGateProfile Lp hLp R hR N
          (prior.frame omega)).answer q.1 =
        BorelStoppingPolicy.feasibleOracleExtension
          (hF.feasibleExactSymmetricJetOracle
            (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
            (hiddenOperator p standardGateProfile Lp R N
              (prior.frame omega))).answer
          (zeroSymmetricExactJet p) q.1
      rw [BorelStoppingPolicy.feasibleOracleExtension_apply]
      exact exact_feasible_answers_eq _ _
        ((finalHiddenExactOracle p hp standardGateProfile Lp hLp R hR N
          (prior.frame omega)).onFeasible
          (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
          (hiddenOperator p standardGateProfile Lp R N (prior.frame omega)))
        (hF.feasibleExactSymmetricJetOracle
          (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
          (hiddenOperator p standardGateProfile Lp R N (prior.frame omega))) q
    _ = _ := runnerOutput_const_environment_eq policy _ _ _ omega () seed

/-- A genuine uniformly successful Borel policy on any ball dimension in the
paper's random-frame regime contradicts the positive-budget obstruction.
Both predicates evaluate the very same saved runner output. -/
theorem not_borelRandomBudgetSurvives_of_positiveObstruction
    (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (hepsilon : 0 < epsilon)
    (N d : ℕ) [NeZero d]
    (hdim : RandomDimensionCondition N d (1 / 4 : ℝ))
    (hobstruction : PositiveRandomBudgetObstruction p hp Lp R D epsilon
      hLp hR hD hepsilon N) :
    ¬ BorelRandomBudgetSurvives
      (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
      N epsilon := by
  rintro ⟨policy, hsuccess⟩
  let data := ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR
  let fill : data.X := ⟨data.x0, data.x0_mem⟩
  let dummy : SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p :=
    zeroSymmetricExactJet p
  let hmdlt : hiddenM N < d :=
    hiddenM_lt_of_randomDimensionCondition (by norm_num) (by norm_num) hdim
  let prior := canonicalHaarPrior hmdlt hR
  let exec := canonicalHaarExecution p hp standardGateProfile Lp hLp R hR
    N d hmdlt policy fill dummy
  obtain ⟨Q, hF, hfailure⟩ :=
    hobstruction d policy fill dummy hdim
  let F := hiddenOperator p standardGateProfile Lp R N (prior.frame Q)
  have hout : ∀ seed : policy.Seed,
      exec.actualOutput Q seed = admissibleBorelOutput data F hF N policy seed := by
    intro seed
    change actualHiddenRunnerOutput prior p hp standardGateProfile Lp hLp hR
        policy fill dummy Q seed = admissibleBorelOutput data F hF N policy seed
    dsimp only [fill, dummy]
    convert actualHiddenRunnerOutput_eq_admissibleBorelOutput prior hp Lp hLp hR
      policy Q hF seed using 1
    apply congrArg (fun point => actualHiddenRunnerOutput prior p hp
      standardGateProfile Lp hLp hR policy point (zeroSymmetricExactJet p) Q seed)
    apply Subtype.ext
    rfl
  have hsuccessF := hsuccess F hF
  have hfailure' : ENNReal.ofReal (3 / 4 : ℝ) ≤ policy.seedMeasure {seed |
      epsilon < tangentResidual data F
        (admissibleBorelOutput data F hF N policy seed).1} := by
    change ENNReal.ofReal (3 / 4 : ℝ) ≤ policy.seedMeasure {seed |
      epsilon < tangentResidual data F (exec.actualOutput Q seed).1} at hfailure
    simpa only [hout] using hfailure
  have hfailureMeasurable : @MeasurableSet policy.Seed policy.seedMeasurable
      {seed : policy.Seed | epsilon < tangentResidual data F
        (admissibleBorelOutput data F hF N policy seed).1} := by
        have hcomp : {seed : policy.Seed | epsilon < tangentResidual data F
            (admissibleBorelOutput data F hF N policy seed).1} =
            {seed : policy.Seed | tangentResidual data F
              (admissibleBorelOutput data F hF N policy seed).1 ≤ epsilon}ᶜ := by
          ext seed
          simp
        rw [hcomp]
        exact hsuccessF.1.compl
  have witness : BorelUniformFailureWitness data N policy epsilon :=
    ⟨F, hF, hfailureMeasurable, by
      have hfrac : (1 / 3 : ℝ≥0∞) < 3 / 4 := by
        apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
        simp only [ENNReal.toReal_div, ENNReal.toReal_one,
          ENNReal.toReal_ofNat]
        norm_num
      have hofReal : (3 / 4 : ℝ≥0∞) = ENNReal.ofReal (3 / 4 : ℝ) := by
        norm_num [ENNReal.ofReal_div_of_pos]
      rw [hofReal] at hfrac
      exact hfrac.trans_le hfailure'⟩
  exact witness.not_randomUniformSuccess data N policy epsilon hsuccess

section ExplicitSuccess

/-- Existence of an actual uniformly successful randomized policy on the
zero-query interval instance. -/
def BorelZeroQueryBudgetSurvives
    (p : ℕ) (hp : 2 ≤ p) (Lp D epsilon : ℝ)
    (hLp : 0 < Lp) (hD : 0 < D) : Prop :=
  ∃ policy : BorelStoppingPolicy.{0, 0, 0}
      (Answer := ZeroQueryAnswer p)
      (intervalVIData p hp Lp D hLp hD).X 0,
    ZeroQueryUniformSuccess p hp Lp D epsilon hLp hD policy

theorem not_borelZeroQueryBudgetSurvives
    (p : ℕ) (hp : 2 ≤ p) (Lp D epsilon : ℝ)
    (hLp : 0 < Lp) (hD : 0 < D) (hepsilon : 0 < epsilon) :
    ¬ BorelZeroQueryBudgetSurvives p hp Lp D epsilon hLp hD := by
  rintro ⟨policy, hsuccess⟩
  obtain ⟨_M, hconclusion⟩ :=
    zeroQueryLowerClaim_proof p hp Lp D epsilon hLp hD hepsilon policy
  exact hconclusion.2.2.2.2.2.2.2.2.2.2 hsuccess

/-- A concrete dimension satisfying the source's random-frame lower-bound
condition at failure parameter `1/4`. -/
def canonicalRandomLowerDimension (N : ℕ) : ℕ :=
  hiddenM N + Nat.ceil
    (2048 * (hiddenM N : ℝ) ^ 3 *
      Real.log (2 * ((hiddenM N : ℝ) ^ 2 + 1) / (1 / 4 : ℝ)))

theorem canonicalRandomLowerDimension_condition (N : ℕ) :
    RandomDimensionCondition N (canonicalRandomLowerDimension N)
      (1 / 4 : ℝ) := by
  dsimp [RandomDimensionCondition, canonicalRandomLowerDimension]
  exact le_rfl

theorem canonicalRandomLowerDimension_pos (N : ℕ) :
    0 < canonicalRandomLowerDimension N := by
  unfold canonicalRandomLowerDimension
  exact lt_of_lt_of_le (hiddenM_pos N) (Nat.le_add_right _ _)

/-- Actual source-model randomized success at budget `N`, separated only
because the zero-query and positive-query adversaries use different public
domains.  In the positive branch a policy may depend on the public dimension,
but must succeed uniformly over every admissible operator in that dimension. -/
def SourceBorelRandomBudgetSuccess
    (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (N : ℕ) : Prop :=
  (N = 0 → BorelZeroQueryBudgetSurvives p hp Lp D epsilon hLp
    (hD.symm ▸ by positivity)) ∧
  (1 ≤ N → ∀ (d : ℕ) [NeZero d],
    RandomDimensionCondition N d (1 / 4 : ℝ) →
    BorelRandomBudgetSurvives
      (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
      N epsilon)

/-- An actual successful Borel family rules out the paper's unified
zero/positive-budget obstruction.  This is the missing implication needed to
use `RandomUniformBudgetSurvives` as a lower-bound consequence rather than as
a surrogate definition of algorithmic success. -/
theorem sourceBorelRandomBudgetSuccess_to_survives
    (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (hepsilon : 0 < epsilon) (N : ℕ)
    (hsuccess : SourceBorelRandomBudgetSuccess p hp Lp R D epsilon
      hLp hR hD N) :
    RandomUniformBudgetSurvives p hp Lp R D epsilon hLp hR hD
      hepsilon N := by
  intro hobstruction
  rcases hobstruction with hzero | hpositive
  · exact not_borelZeroQueryBudgetSurvives p hp Lp D epsilon hLp
      (hD.symm ▸ by positivity) hepsilon (hsuccess.1 hzero.1)
  · let d := canonicalRandomLowerDimension N
    letI : NeZero d := ⟨Nat.ne_of_gt (canonicalRandomLowerDimension_pos N)⟩
    have hdim : RandomDimensionCondition N d (1 / 4 : ℝ) :=
      canonicalRandomLowerDimension_condition N
    have hball := hsuccess.2 hpositive.1 d hdim
    exact not_borelRandomBudgetSurvives_of_positiveObstruction p hp Lp R D
      epsilon hLp hR hD hepsilon N d hdim hpositive.2 hball

/-- Direct all-budget source lower bound from existence of actual uniformly
successful randomized Borel policies. -/
theorem sourceBorelRandomSuccessfulBudget_lower
    (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (hepsilon : 0 < epsilon)
    (hQ : 2 ≤ deterministicConditionNumber p Lp D epsilon)
    (N : ℕ)
    (hsuccess : SourceBorelRandomBudgetSuccess p hp Lp R D epsilon
      hLp hR hD N) :
    sourceMainLowerConstant p *
        deterministicConditionNumber p Lp D epsilon ^
          deterministicRateExponent p ≤ (N : ℝ) := by
  exact randomUniformSuccessfulBudget_lower p hp Lp R D epsilon hLp hR hD
    hepsilon hQ N (sourceBorelRandomBudgetSuccess_to_survives p hp Lp R D
      epsilon hLp hR hD hepsilon N hsuccess)

/-- Deterministic source success uses the identical Borel policies, with the
additional singleton-seed condition. -/
def SourceBorelDeterministicBudgetSuccess
    (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (N : ℕ) : Prop :=
  (N = 0 → ∃ policy : BorelStoppingPolicy.{0, 0, 0}
      (Answer := ZeroQueryAnswer p)
      (intervalVIData p hp Lp D hLp (hD.symm ▸ by positivity)).X 0,
    policy.IsDeterministic ∧
      ZeroQueryUniformSuccess p hp Lp D epsilon hLp
        (hD.symm ▸ by positivity) policy) ∧
  (1 ≤ N → ∀ (d : ℕ) [NeZero d],
    RandomDimensionCondition N d (1 / 4 : ℝ) →
    BorelDeterministicBudgetSurvives
      (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
      N epsilon)

/-- Same-policy deterministic-to-randomized promotion for the full source
family: the positive-budget branch uses the exact policy object and only
equips its singleton seed with its existing probability law. -/
theorem sourceBorelRandomBudgetSuccess_of_deterministic
    (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (N : ℕ) :
    SourceBorelDeterministicBudgetSuccess p hp Lp R D epsilon hLp hR hD N →
      SourceBorelRandomBudgetSuccess p hp Lp R D epsilon hLp hR hD N := by
  intro hdet
  constructor
  · intro hN
    obtain ⟨policy, _hseed, hsuccess⟩ := hdet.1 hN
    exact ⟨policy, hsuccess⟩
  · intro hN d _instD hdim
    exact borelRandomBudgetSurvives_of_deterministic
      (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
      N epsilon (hdet.2 hN d hdim)

theorem sourceBorelDeterministicSuccessfulBudget_lower
    (p : ℕ) (hp : 2 ≤ p)
    (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hD : D = 2 * R) (hepsilon : 0 < epsilon)
    (hQ : 2 ≤ deterministicConditionNumber p Lp D epsilon)
    (N : ℕ)
    (hsuccess : SourceBorelDeterministicBudgetSuccess p hp Lp R D epsilon
      hLp hR hD N) :
    sourceMainLowerConstant p *
        deterministicConditionNumber p Lp D epsilon ^
          deterministicRateExponent p ≤ (N : ℝ) := by
  exact sourceBorelRandomSuccessfulBudget_lower p hp Lp R D epsilon hLp hR
    hD hepsilon hQ N
      (sourceBorelRandomBudgetSuccess_of_deterministic p hp Lp R D epsilon
        hLp hR hD N hsuccess)

end ExplicitSuccess

end

end LeanArticleAudit.Pilot
