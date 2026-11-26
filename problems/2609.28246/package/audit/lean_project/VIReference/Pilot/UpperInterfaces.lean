import VIReference.Pilot.Execution

/-!
# Executable certified solver interfaces

This file implements the two interfaces in `def:interfaces`.  Algorithms are
syntax trees fixed from public inputs.  The unknown operator enters only in
`CappedExactJetCall.execute`, through an exact oracle.  Fuel is checked before
each query, so exhaustion cannot occur after an uncontrolled descendant call.
-/

open Set
open scoped RealInnerProductSpace

namespace VIReference.Pilot

noncomputable section

universe u v w

section FeasibleOracle

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Exact jet oracle on the feasible points that an upper-bound program is
allowed to query. This matches the source's neighbourhood regularity. -/
structure FeasibleExactSymmetricJetOracle
    (data : VIPublicData E) (F : E → E) where
  answer : data.X → SymmetricExactJet E data.p
  exact : ∀ point (j : Fin data.p),
    ((answer point) j).1 = iteratedFDeriv ℝ j.1 F point.1

/-- Restriction of the older globally typed oracle to legal query points. -/
def ExactSymmetricJetOracle.onFeasible
    (data : VIPublicData E) (F : E → E)
    (oracle : ExactSymmetricJetOracle data F) :
    FeasibleExactSymmetricJetOracle data F where
  answer point := oracle.answer point.1
  exact point j := oracle.exact point.1 j

end FeasibleOracle

/-- A finite oracle program. `return none` is an ordinary reported failure;
`query` is the only constructor allowed to inspect an oracle answer. -/
inductive ExactJetProgram (X Answer Output : Type*) where
  | halt (result : Option Output)
  | query (point : X) (next : Answer → ExactJetProgram X Answer Output)

/-- Observable result of fuelled execution.  `exhausted` is distinct from an
algorithmically reported failure. -/
inductive CappedRunResult (Output : Type*) where
  | exhausted
  | finished (queriesUsed : ℕ) (result : Option Output)

namespace ExactJetProgram

/-- Big-step semantics exposing exactly the number of oracle calls on the
executed branch. -/
inductive Evaluates {X Answer Output : Type*} (oracle : X → Answer) :
    ExactJetProgram X Answer Output → ℕ → Option Output → Prop where
  | halt (result) : Evaluates oracle (.halt result) 0 result
  | query (point) (next) (used) (result)
      (hnext : Evaluates oracle (next (oracle point)) used result) :
      Evaluates oracle (.query point next) (used + 1) result

/-- Monadic sequencing. A reported failure propagates without running the
continuation; successful output may determine all later query points. -/
def bind {X Answer A B : Type*} :
    ExactJetProgram X Answer A →
      (A → ExactJetProgram X Answer B) → ExactJetProgram X Answer B
  | .halt none, _ => .halt none
  | .halt (some value), next => next value
  | .query point more, next => .query point (fun answer => bind (more answer) next)

/-- Turn exhaustion of a local subcall into its explicit reported-failure
result. Thus a parent program can continue to another trial while every child
still has its own preinstalled cap. -/
def locallyCapped {X Answer Output : Type*} :
    ℕ → ExactJetProgram X Answer Output → ExactJetProgram X Answer Output
  | _, .halt result => .halt result
  | 0, .query _ _ => .halt none
  | fuel + 1, .query point next =>
      .query point (fun answer => locallyCapped fuel (next answer))

/-- Try `first`; only its explicit failure branch runs `fallback`. -/
def orElse {X Answer Output : Type*}
    (first fallback : ExactJetProgram X Answer Output) :
    ExactJetProgram X Answer Output :=
  match first with
  | .halt none => fallback
  | .halt (some value) => .halt (some value)
  | .query point next => .query point (fun answer => orElse (next answer) fallback)

/-- Execute with a shared active cap.  In the `fuel = 0, query` branch the
oracle is not evaluated.  Recursive descendants receive the decremented cap. -/
def runWithFuel {X Answer Output : Type*} (oracle : X → Answer) :
    (fuel : ℕ) → ExactJetProgram X Answer Output → CappedRunResult Output
  | _, .halt result => .finished 0 result
  | 0, .query _ _ => .exhausted
  | fuel + 1, .query point next =>
      match runWithFuel oracle fuel (next (oracle point)) with
      | .exhausted => .exhausted
      | .finished used result => .finished (used + 1) result

theorem runWithFuel_finished_queries_le {X Answer Output : Type*}
    (oracle : X → Answer) (program : ExactJetProgram X Answer Output)
    {fuel used : ℕ} {result : Option Output}
    (hrun : program.runWithFuel oracle fuel =
      CappedRunResult.finished used result) :
    used ≤ fuel := by
  induction fuel generalizing program used result with
  | zero =>
      cases program <;> simp [runWithFuel] at hrun <;> omega
  | succ fuel ih =>
      cases program with
      | halt output =>
          simp [runWithFuel] at hrun
          omega
      | query point next =>
          simp only [runWithFuel] at hrun
          split at hrun
          · contradiction
          · rename_i childUsed childResult hchild
            cases hrun
            exact Nat.succ_le_succ (ih _ hchild)

theorem Evaluates.runWithFuel_eq {X Answer Output : Type*}
    {oracle : X → Answer} {program : ExactJetProgram X Answer Output}
    {used : ℕ} {result : Option Output}
    (heval : Evaluates oracle program used result) {fuel : ℕ}
    (hused : used ≤ fuel) :
    program.runWithFuel oracle fuel = .finished used result := by
  induction heval generalizing fuel with
  | halt result => simp [runWithFuel]
  | query point next used result hnext ih =>
      obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      simp only [runWithFuel]
      rw [ih (by omega)]

theorem evaluates_of_runWithFuel_finished {X Answer Output : Type*}
    {oracle : X → Answer} {program : ExactJetProgram X Answer Output}
    {fuel used : ℕ} {result : Option Output}
    (hrun : program.runWithFuel oracle fuel = .finished used result) :
    Evaluates oracle program used result := by
  induction fuel generalizing program used result with
  | zero =>
      cases program with
      | halt output =>
          simp [runWithFuel] at hrun
          rcases hrun with ⟨rfl, rfl⟩
          exact .halt _
      | query point next => simp [runWithFuel] at hrun
  | succ fuel ih =>
      cases program with
      | halt output =>
          simp [runWithFuel] at hrun
          rcases hrun with ⟨rfl, rfl⟩
          exact .halt _
      | query point next =>
          simp only [runWithFuel] at hrun
          cases hchild : runWithFuel oracle fuel (next (oracle point)) with
          | exhausted => simp [hchild] at hrun
          | finished childUsed childResult =>
              rw [hchild] at hrun
              cases hrun
              exact .query point next _ _ (ih hchild)

theorem Evaluates.locallyCapped {X Answer Output : Type*}
    {oracle : X → Answer} {program : ExactJetProgram X Answer Output}
    {used : ℕ} {result : Option Output}
    (heval : Evaluates oracle program used result) {cap : ℕ}
    (hused : used ≤ cap) :
    Evaluates oracle (program.locallyCapped cap) used result := by
  induction heval generalizing cap with
  | halt result =>
      cases cap <;> exact .halt _
  | query point next used result hnext ih =>
      obtain ⟨cap, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : cap ≠ 0)
      exact .query point _ used result (ih (by omega))

theorem Evaluates.bind {X Answer A B : Type*}
    {oracle : X → Answer} {program : ExactJetProgram X Answer A}
    {used₁ used₂ : ℕ} {value : A} {result : Option B}
    {next : A → ExactJetProgram X Answer B}
    (hfirst : Evaluates oracle program used₁ (some value))
    (hnext : Evaluates oracle (next value) used₂ result) :
    Evaluates oracle (program.bind next) (used₁ + used₂) result := by
  generalize hopt : (some value : Option A) = option at hfirst
  induction hfirst generalizing value used₂ result with
  | halt option =>
      cases hopt
      change Evaluates oracle (next value) (0 + used₂) result
      simpa using hnext
  | query point more used option hmore ih =>
      have htail := ih hnext hopt
      have hx := Evaluates.query point
        (fun answer => (more answer).bind next) (used + used₂) result htail
      change Evaluates oracle
        (.query point (fun answer => (more answer).bind next))
        (used + 1 + used₂) result
      convert hx using 1 <;> omega

end ExactJetProgram

section Certificates

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Successful upper-bound output: a feasible point, a proposed outward
normal, and the already evaluated operator value at that point. -/
structure EvaluatedNormalCertificate (data : VIPublicData E) where
  point : data.X
  normal : E
  value : E

/-- Kernel-level verification of a returned certificate.  In particular,
`value_eq` rules out claiming an unevaluated or fabricated value. -/
def EvaluatedNormalCertificate.IsVerifiedFor (data : VIPublicData E)
    (F : E → E) (epsilon : ℝ) (cert : EvaluatedNormalCertificate data) : Prop :=
  cert.normal ∈ normalCone data.X cert.point.1 ∧
  cert.value = F cert.point.1 ∧
  ‖cert.value + cert.normal‖ ≤ epsilon

theorem EvaluatedNormalCertificate.tangentResidual_le
    (data : VIPublicData E) (F : E → E) (epsilon : ℝ)
    (cert : EvaluatedNormalCertificate data)
    (hcert : cert.IsVerifiedFor data F epsilon) :
    tangentResidual data F cert.point.1 ≤ epsilon := by
  have hmem : F cert.point.1 + cert.normal ∈
      (fun n => F cert.point.1 + n) '' normalCone data.X cert.point.1 :=
    ⟨cert.normal, hcert.1, rfl⟩
  calc
    tangentResidual data F cert.point.1 ≤
        dist 0 (F cert.point.1 + cert.normal) :=
      Metric.infDist_le_dist_of_mem hmem
    _ = ‖cert.value + cert.normal‖ := by
      rw [dist_zero_left, hcert.2.1]
    _ ≤ epsilon := hcert.2.2

end Certificates

section Calls

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A solver call installs its finite cap before execution. -/
structure CappedExactJetCall (data : VIPublicData E) where
  cap : ℕ
  program : ExactJetProgram data.X (SymmetricExactJet E data.p)
    (EvaluatedNormalCertificate data)

def CappedExactJetCall.execute (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F)
    (call : CappedExactJetCall data) :
    CappedRunResult (EvaluatedNormalCertificate data) :=
  call.program.runWithFuel oracle.answer call.cap

theorem CappedExactJetCall.finished_queries_le_cap
    (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F)
    (call : CappedExactJetCall data) {used : ℕ}
    {result : Option (EvaluatedNormalCertificate data)}
    (hrun : call.execute data F oracle = .finished used result) :
    used ≤ call.cap := by
  exact ExactJetProgram.runWithFuel_finished_queries_le _ _ hrun

end Calls

section Costs

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- `Q_R = L_p R^p / epsilon`. -/
def residualCondition (data : VIPublicData E) (R epsilon : ℝ) : ℝ :=
  data.Lp * R ^ data.p / epsilon

/-- `L_A(R,epsilon)` from Equation (LA). -/
def residualLog (data : VIPublicData E) (R epsilon : ℝ) : ℝ :=
  1 + Real.log (2 + data.D / R + residualCondition data R epsilon)

/-- `L_S(mu,delta)` from Equation (LS). -/
def strongLog (data : VIPublicData E) (mu delta : ℝ) : ℝ :=
  1 + Real.log (2 + data.Lp * data.D ^ (data.p - 1) / mu +
    data.Lp * data.D ^ data.p / delta + mu * data.D / delta)

def residualInterfaceCost (data : VIPublicData E)
    (C alpha : ℝ) (b : ℕ) (R epsilon : ℝ) : ℝ :=
  C * (1 + (residualCondition data R epsilon) ^ alpha) *
    (residualLog data R epsilon) ^ b

def strongInterfaceCost (data : VIPublicData E)
    (C gamma : ℝ) (b : ℕ) (r mu delta : ℝ) : ℝ :=
  C * (1 + (data.Lp * r ^ (data.p - 1) / mu) ^ gamma) *
    (strongLog data mu delta) ^ b

/-- Strong monotonicity on the original public domain. -/
def StronglyMonotoneOn (data : VIPublicData E) (G : E → E) (mu : ℝ) : Prop :=
  ∀ x ∈ data.X, ∀ y ∈ data.X,
    mu * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y)

end Costs

section Implementations

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Executable residual-solver implementation.  Its `solve` field sees only
public data, a feasible center, and numerical inputs—not the unknown `F`. -/
structure ResidualSolver (data : VIPublicData E) where
  leadingConstant : ℝ
  leadingConstant_pos : 0 < leadingConstant
  solve : data.X → ℝ → ℝ → CappedExactJetCall data

/-- Executable strong-solver implementation without a supplied distance. -/
structure StrongSolver (data : VIPublicData E) where
  leadingConstant : ℝ
  leadingConstant_pos : 0 < leadingConstant
  solve : data.X → ℝ → ℝ → CappedExactJetCall data

/-- A residual implementation family for fixed order `p`.  The one leading
constant is chosen before *all* dimensions, domains, Lipschitz bounds, and
unknown operators; hence it can depend on `p` but not on an instance. -/
structure ResidualSolverFamily (p : ℕ) where
  leadingConstant : ℝ
  leadingConstant_pos : 0 < leadingConstant
  solve : ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E), data.p = p →
      data.X → ℝ → ℝ → CappedExactJetCall data

/-- Strong-solver family with the same fixed-`p` leading-constant scope. -/
structure StrongSolverFamily (p : ℕ) where
  leadingConstant : ℝ
  leadingConstant_pos : 0 < leadingConstant
  solve : ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E), data.p = p →
      data.X → ℝ → ℝ → CappedExactJetCall data

def ResidualSolverFamily.atData {p : ℕ} (family : ResidualSolverFamily.{u} p)
    (data : VIPublicData E) (hp : data.p = p) : ResidualSolver data where
  leadingConstant := family.leadingConstant
  leadingConstant_pos := family.leadingConstant_pos
  solve := family.solve E data hp

def StrongSolverFamily.atData {p : ℕ} (family : StrongSolverFamily.{u} p)
    (data : VIPublicData E) (hp : data.p = p) : StrongSolver data where
  leadingConstant := family.leadingConstant
  leadingConstant_pos := family.leadingConstant_pos
  solve := family.solve E data hp

/-- Complete semantic contract of `A_(alpha,b)`.  Correctness under a true
distance promise and the cap bound are separate from the implementation.
`no_false_success` applies to every operator in the public problem class even
when the *distance* promise is false; it is intentionally not a contract for
arbitrary nonsmooth functions outside that class. -/
def ResidualSolver.SatisfiesInterface (data : VIPublicData E)
    (A : ResidualSolver data) (alpha : ℝ) (b : ℕ) : Prop :=
  (∀ center R epsilon,
    0 < R → R ≤ data.D → 0 < epsilon →
      ((A.solve center R epsilon).cap : ℝ) ≤
        residualInterfaceCost data A.leadingConstant alpha b R epsilon) ∧
  (∀ (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
      center R epsilon used cert, IsAdmissibleOperator data F →
    0 < R → 0 < epsilon →
    (A.solve center R epsilon).execute data F oracle =
        .finished used (some cert) →
      cert.IsVerifiedFor data F epsilon) ∧
  (∀ (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
      center R epsilon, IsAdmissibleOperator data F →
    0 < R → R ≤ data.D → 0 < epsilon →
    ∀ zStar, IsVISolution data F zStar → ‖center.1 - zStar‖ ≤ R →
      ∃ used cert,
        (A.solve center R epsilon).execute data F oracle =
          .finished used (some cert) ∧
        cert.IsVerifiedFor data F epsilon ∧
        (used : ℝ) ≤
          residualInterfaceCost data A.leadingConstant alpha b R epsilon)

/-- Complete semantic contract of `S_(gamma,b)`.  The implementation receives
`mu,delta` but not the analytical distance `r`; only the achieved-query bound
mentions the true distance.  No-false-success remains independent of all
distance/strong-monotonicity promises, but is scoped to the problem class. -/
def StrongSolver.SatisfiesInterface (data : VIPublicData E)
    (S : StrongSolver data) (gamma : ℝ) (b : ℕ) : Prop :=
  (∀ (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
      center mu delta used cert, IsAdmissibleOperator data G →
    0 < mu → 0 < delta →
    (S.solve center mu delta).execute data G oracle =
        .finished used (some cert) →
      cert.IsVerifiedFor data G delta) ∧
  (∀ (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
      center mu delta, IsAdmissibleOperator data G →
    0 < mu → 0 < delta → StronglyMonotoneOn data G mu →
    ∀ zStar, IsVISolution data G zStar →
      ∃ used cert,
        (S.solve center mu delta).execute data G oracle =
          .finished used (some cert) ∧
        cert.IsVerifiedFor data G delta ∧
        (used : ℝ) ≤ strongInterfaceCost data S.leadingConstant gamma b
          ‖center.1 - zStar‖ mu delta)

def ResidualSolverFamily.SatisfiesInterface {p : ℕ}
    (family : ResidualSolverFamily.{u} p) (alpha : ℝ) (b : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p),
    (family.atData data hp).SatisfiesInterface data alpha b

def StrongSolverFamily.SatisfiesInterface {p : ℕ}
    (family : StrongSolverFamily.{u} p) (gamma : ℝ) (b : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p),
    (family.atData data hp).SatisfiesInterface data gamma b

end Implementations

section InterfaceContract

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Hash-facing expansion of both algorithm contracts in `def:interfaces`.
This theorem does not assert existence of a solver; it certifies precisely
what it means for an executable implementation to have either interface. -/
def AlgorithmInterfacesClaim : Prop :=
  ∀ (p : ℕ),
    (∀ (A : ResidualSolverFamily.{u} p) (alpha : ℝ) (b : ℕ),
      A.SatisfiesInterface alpha b ↔
        ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p),
          (A.atData data hp).SatisfiesInterface data alpha b) ∧
    (∀ (S : StrongSolverFamily.{u} p) (gamma : ℝ) (b : ℕ),
      S.SatisfiesInterface gamma b ↔
        ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p),
          (S.atData data hp).SatisfiesInterface data gamma b)

theorem algorithmInterfacesClaim_proof : AlgorithmInterfacesClaim := by
  intro p
  constructor <;> intro solver exponent b <;> rfl

end InterfaceContract

end

end VIReference.Pilot
