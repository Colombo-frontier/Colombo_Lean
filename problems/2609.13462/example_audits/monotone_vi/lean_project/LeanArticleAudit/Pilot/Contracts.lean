import LeanArticleAudit.Pilot.Execution

/-!
# Source-faithful contracts for the five-claim pilot

These declarations make the paper-to-Lean translation inspectable before any
proof is credited.  In particular, the Halpern assumptions are not replaced by
the estimates to be proved, and `GateProfile` contains only the assumptions on
`ρ` stated immediately before `lem:gate`.
-/

open Set MeasureTheory intervalIntegral
open scoped ContDiff

namespace LeanArticleAudit.Pilot

section DefinitionContracts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Auditable expansion of `def:class`.  This `Iff.rfl` theorem places the full
definition in a theorem signature, so the external statement-hash gate binds
the mathematical body rather than only the name of a structure. -/
theorem class_contract (data : VIPublicData E) (F : E → E) :
    IsAdmissibleOperator data F ↔
      ((∃ U : Set E, IsOpen U ∧ data.X ⊆ U ∧
          ContDiffOn ℝ (data.p - 1) F U) ∧
        ((x : E) → x ∈ data.X → (y : E) → y ∈ data.X →
          0 ≤ inner ℝ (F x - F y) (x - y)) ∧
        ((x : E) → x ∈ data.X → (y : E) → y ∈ data.X →
          ‖iteratedFDeriv ℝ (data.p - 1) F x -
            iteratedFDeriv ℝ (data.p - 1) F y‖ ≤ data.Lp * ‖x - y‖)) ∧
      (∀ xStar : E, IsVISolution data F xStar ↔
        xStar ∈ data.X ∧
          ∀ x ∈ data.X, 0 ≤ inner ℝ (F xStar) (x - xStar)) := by
  constructor
  · intro h
    exact ⟨⟨h.regularity, h.monotone_on, h.top_derivative_lipschitz⟩,
      fun _ => Iff.rfl⟩
  · rintro ⟨⟨hreg, hmono, hlip⟩, _hsolution⟩
    exact ⟨hreg, hmono, hlip⟩

end DefinitionContracts

section PolicyContract

variable {E Answer : Type*} [MeasurableSpace E] [MeasurableSpace Answer]

/-- Type-level consequences that must hold for every policy admitted by
`def:policy`: a probability seed, measurable total rules, feasible queries and
an arbitrary feasible output at the fixed query cap. -/
theorem policy_contract {X : Set E} {budget : ℕ}
    (policy : BorelOraclePolicy (Answer := Answer) X budget) :
    @IsProbabilityMeasure policy.Seed policy.seedMeasurable policy.seedMeasure ∧
      (∀ n, @Measurable
        (policy.Seed × OracleHistory X Answer n.1) X
        (MeasurableSpace.prod policy.seedMeasurable inferInstance) inferInstance
        (policy.queryRule n)) ∧
      @Measurable
        (policy.Seed × OracleHistory X Answer budget) X
        (MeasurableSpace.prod policy.seedMeasurable inferInstance) inferInstance
        policy.outputRule := by
  exact ⟨policy.seedProbability, policy.queryRule_measurable,
    policy.outputRule_measurable⟩

end PolicyContract

section ExactPolicyContract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]

/-- Full hash-bound expansion of `def:policy`.

Besides the probability/measurability fields, this statement binds the
singleton deterministic specialization, the connection between every returned
jet and the actual unknown `F`, the per-run tangent-residual success predicate,
and the equivalence between genuine early stopping and the paper's padded
fixed-history normal form. -/
theorem exact_policy_contract (data : VIPublicData E) (epsilon : ℝ)
    (budget : ℕ)
    (policy : BorelStoppingPolicy (Answer := SymmetricExactJet E data.p)
      data.X budget) :
    @IsProbabilityMeasure policy.Seed policy.seedMeasurable policy.seedMeasure ∧
      (∀ n, @Measurable
        (policy.Seed × OracleHistory data.X (SymmetricExactJet E data.p) n.1)
        (OracleAction data.X)
        (MeasurableSpace.prod policy.seedMeasurable inferInstance) inferInstance
        (policy.rule n)) ∧
      (∀ state : policy.Seed ×
          OracleHistory data.X (SymmetricExactJet E data.p) budget,
        ∃ output : data.X,
          policy.rule ⟨budget, Nat.lt_add_one budget⟩ state = Sum.inl output) ∧
      (policy.IsDeterministic ↔
        Nonempty policy.Seed ∧ Subsingleton policy.Seed) ∧
      (∀ (F : E → E) (oracle : ExactSymmetricJetOracle data F)
          (x : E) (j : Fin data.p),
        ((oracle.answer x) j).1 = iteratedFDeriv ℝ j.1 F x) ∧
      (∀ (F : E → E) (oracle : ExactSymmetricJetOracle data F)
          (seed : policy.Seed) (n : ℕ) (hn : n ≤ budget)
          (history : OracleHistory data.X (SymmetricExactJet E data.p) n)
          (output : data.X),
        policy.RunSucceedsOn data F epsilon oracle seed n hn history output ↔
          policy.IsUnpaddedRun oracle.answer seed n hn history output ∧
            tangentResidual data F output.1 ≤ epsilon) ∧
      (∀ (F : E → E) (oracle : ExactSymmetricJetOracle data F)
          (seed : policy.Seed) (output : data.X),
        (∃ n, ∃ hn : n ≤ budget,
          ∃ history : OracleHistory data.X (SymmetricExactJet E data.p) n,
            policy.IsUnpaddedRun oracle.answer seed n hn history output) ↔
        ∃ history : OracleHistory data.X (SymmetricExactJet E data.p) budget,
          policy.IsPaddedRun oracle.answer seed history output) := by
  refine ⟨policy.seedProbability, policy.rule_measurable, policy.cap_stops,
    Iff.rfl, ?_, ?_, ?_⟩
  · intro F oracle x j
    exact oracle.exact x j
  · intro F oracle seed n hn history output
    rfl
  · intro F oracle seed output
    exact policy.unpadded_iff_padded oracle.answer seed
      ⟨data.x0, data.x0_mem⟩ output

end ExactPolicyContract

section HalpernContracts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Real harmonic number `H_t = ∑_{i=1}^t 1/i`. -/
noncomputable def harmonicR : ℕ → ℝ
  | 0 => 0
  | n + 1 => harmonicR n + 1 / (n + 1 : ℝ)

/-- The exact firm-nonexpansiveness inequality used in the article. -/
def FirmlyNonexpansive (P : E → E) : Prop :=
  ∀ x y, ‖P x - P y‖ ^ 2 + ‖(x - P x) - (y - P y)‖ ^ 2 ≤ ‖x - y‖ ^ 2

/-- Exact Halpern orbit, written with nonzero denominators in the same form as
Equation (exact-halpern). -/
def IsHalpernOrbit (P : E → E) (x0 : E) (x y : ℕ → E) : Prop :=
  x 0 = x0 ∧
  (∀ t, y t = P (x t)) ∧
  (∀ t, x (t + 1) =
    (1 / (t + 2 : ℝ)) • x0 + ((t + 1 : ℝ) / (t + 2 : ℝ)) • y t)

/-- Complete conclusion of `lem:firstdiff`, including both estimates, the exact
identity, and the `c_t` estimate. -/
def FirstDifferenceConclusion (x0 : E) (x y : ℕ → E) (R : ℝ) : Prop :=
  (∀ t, 1 ≤ t →
    ‖y t - y (t - 1)‖ ≤ ‖x t - x (t - 1)‖ ∧
    ‖x t - x (t - 1)‖ ≤ 2 * R * harmonicR t / (t + 1 : ℝ) ∧
    ‖x t - y t‖ ≤ 2 * R * (1 + harmonicR (t + 1)) / (t + 1 : ℝ)) ∧
  (∀ t, 2 ≤ t →
    x t - x (t - 1) =
      ((t : ℝ) / (t + 1 : ℝ)) • (y (t - 1) - y (t - 2)) +
      (1 / ((t : ℝ) * (t + 1 : ℝ))) • (y (t - 2) - x0) ∧
    ‖(x t - x (t - 1)) - (y (t - 1) - y (t - 2))‖ ≤
      2 * R * (1 + harmonicR (t - 1)) /
        ((t : ℝ) * (t + 1 : ℝ)))

/-- Source-faithful proposition corresponding to `lem:firstdiff`. -/
def FirstDifferenceClaim (P : E → E) (zStar x0 : E) (x y : ℕ → E)
    (R : ℝ) : Prop :=
    FirmlyNonexpansive P → P zStar = zStar → IsHalpernOrbit P x0 x y →
    ‖x0 - zStar‖ ≤ R → FirstDifferenceConclusion x0 x y R

/-- Hashable expansion of the source proposition.  This theorem proves only
that the named contract expands to the displayed statement; it is deliberately
classified as `statement_only`, not as a proof of `lem:firstdiff`. -/
theorem firstDifference_contract (P : E → E) (zStar x0 : E)
    (x y : ℕ → E) (R : ℝ) :
    FirstDifferenceClaim P zStar x0 x y R ↔
      FirmlyNonexpansive P → P zStar = zStar → IsHalpernOrbit P x0 x y →
      ‖x0 - zStar‖ ≤ R → FirstDifferenceConclusion x0 x y R := Iff.rfl

/-- Complete boxed conclusion of `lem:second-energy`. -/
def SecondEnergyConclusion (y : ℕ → E) (R : ℝ) : Prop :=
  ∀ k ell, 2 ≤ k → k ≤ ell → ell ≤ 2 * k - 1 →
    (∑ t ∈ Finset.Icc k ell,
      ‖y t - (2 : ℝ) • y (t - 1) + y (t - 2)‖ ^ 2) ≤
      64 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) / (k : ℝ) ^ 2

/-- Source-faithful proposition corresponding to `lem:second-energy`. -/
def SecondEnergyClaim (P : E → E) (zStar x0 : E) (x y : ℕ → E)
    (R : ℝ) : Prop :=
    FirmlyNonexpansive P → P zStar = zStar → IsHalpernOrbit P x0 x y →
    ‖x0 - zStar‖ ≤ R → SecondEnergyConclusion y R

/-- Hashable expansion of `lem:second-energy`; not a proof of the claim. -/
theorem secondEnergy_contract (P : E → E) (zStar x0 : E)
    (x y : ℕ → E) (R : ℝ) :
    SecondEnergyClaim P zStar x0 x y R ↔
      FirmlyNonexpansive P → P zStar = zStar → IsHalpernOrbit P x0 x y →
      ‖x0 - zStar‖ ≤ R → SecondEnergyConclusion y R := Iff.rfl

end HalpernContracts

section GateContract

/-- Only the assumptions imposed on `ρ` immediately before `lem:gate`. -/
structure GateProfile where
  rho : ℝ → ℝ
  smooth : ContDiff ℝ ∞ rho
  even : Function.Even rho
  range : ∀ u, 0 ≤ rho u ∧ rho u ≤ 1
  zero_core : ∀ u, |u| ≤ (1 / 2 : ℝ) → rho u = 0
  one_tail : ∀ u, 1 ≤ |u| → rho u = 1

/-- `h_τ(s)=τ∫₀^(s/τ)ρ(u)du`. -/
noncomputable def gate (profile : GateProfile) (tau s : ℝ) : ℝ :=
  tau * ∫ u in 0..(s / tau), profile.rho u

/-- `b_τ=τ∫₀¹(1-ρ(u))du`. -/
noncomputable def gateShift (profile : GateProfile) (tau : ℝ) : ℝ :=
  tau * ∫ u in 0..1, (1 - profile.rho u)

/-- The supremum bound for the derivative of `ρ` used in the Lipschitz
conclusion.  Proving that this range is bounded from the profile's smoothness
and constant tails is part of the pending gate proof. -/
noncomputable def gateBp (p : ℕ) (profile : GateProfile) : ℝ :=
  max 1 (sSup (Set.range fun u => |iteratedDeriv (p - 1) profile.rho u|))

/-- Complete conclusion of `lem:gate`; `ContDiff ℝ ∞` is `C∞`, and the final
pointwise inequality is the metric definition of the claimed Lipschitz bound. -/
def GateConclusion (p : ℕ) (profile : GateProfile) (tau : ℝ) : Prop :=
  Function.Odd (gate profile tau) ∧
  ContDiff ℝ ∞ (gate profile tau) ∧
  (∀ s, 0 ≤ deriv (gate profile tau) s ∧ deriv (gate profile tau) s ≤ 1 ∧
    |gate profile tau s| ≤ |s| ∧ |s - gate profile tau s| ≤ tau ∧
    gate profile tau s ≥ s - tau) ∧
  (∀ s, |s| ≤ tau / 2 → gate profile tau s = 0) ∧
  (∀ n s, |s| ≤ tau / 2 → iteratedDeriv n (gate profile tau) s = 0) ∧
  (∀ x y,
    |iteratedDeriv (p - 1) (gate profile tau) x -
      iteratedDeriv (p - 1) (gate profile tau) y| ≤
      gateBp p profile * tau ^ (1 - (p : ℤ)) * |x - y|) ∧
  (∀ s, tau ≤ s → gate profile tau s = s - gateShift profile tau) ∧
  tau / 2 ≤ gateShift profile tau ∧ gateShift profile tau ≤ tau

/-- Source-faithful proposition corresponding to `lem:gate`. -/
def GateClaim (p : ℕ) (profile : GateProfile) (tau : ℝ) : Prop :=
    2 ≤ p → 0 < tau →
    GateConclusion p profile tau

/-- Hashable expansion of `lem:gate`; not a proof of the claim. -/
theorem gate_contract (p : ℕ) (profile : GateProfile) (tau : ℝ) :
    GateClaim p profile tau ↔ 2 ≤ p → 0 < tau →
      GateConclusion p profile tau := Iff.rfl

end GateContract

end LeanArticleAudit.Pilot
