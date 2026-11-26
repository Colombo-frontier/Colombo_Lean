import LeanArticleAudit.Pilot.Contracts
import LeanArticleAudit.Pilot.MainAssembly
import LeanArticleAudit.Pilot.UpperBorelCallOutcome
import LeanArticleAudit.Pilot.UpperHierarchy

/-!
# Borel invariant for the finite upper hierarchy

The original finite hierarchy retained only the numerical solver interface.
Here the induction invariant additionally retains measurability of the full
terminal certificate/query observation.  This is the compositional invariant
needed by boost and restart; its weaker action projection then compiles the
final capped call to the frozen `def:policy` structure.
-/

open Set MeasureTheory

namespace LeanArticleAudit.Pilot

noncomputable section

/-- A residual family carrying both its executable complexity interface and
the full Borel outcome property needed by later program transformations. -/
def HasBorelResidualSolver (p : ℕ) (alpha : ℝ) (b : ℕ) : Prop :=
  ∃ A : ResidualSolverFamily.{0} p,
    A.SatisfiesInterface alpha b ∧ A.IsBorel

/-- Strong-solver analogue of `HasBorelResidualSolver`. -/
def HasBorelStrongSolver (p : ℕ) (gamma : ℝ) (b : ℕ) : Prop :=
  ∃ S : StrongSolverFamily.{0} p,
    S.SatisfiesInterface gamma b ∧ S.IsBorel

/-- Honest compositional residual invariant: for fixed scalar inputs, both
the ordinary and anchor-varying calls are jointly Borel after installing
their actual (possibly center-dependent) caps. -/
def HasJointBorelResidualSolver (p : ℕ) (alpha : ℝ) (b : ℕ) : Prop :=
  ∃ A : ResidualSolverFamily.{0} p,
    A.SatisfiesInterface alpha b ∧ A.HasJointBorelCappedOutcome

/-- Capped and anchor-uniform strong-solver analogue. -/
def HasJointBorelStrongSolver (p : ℕ) (gamma : ℝ) (b : ℕ) : Prop :=
  ∃ S : StrongSolverFamily.{0} p,
    S.SatisfiesInterface gamma b ∧ S.HasJointBorelCappedOutcome

theorem HasBorelResidualSolver.toHasResidualSolver
    {p : ℕ} {alpha : ℝ} {b : ℕ}
    (h : HasBorelResidualSolver p alpha b) :
    HasResidualSolver p alpha b := by
  obtain ⟨A, hA, _⟩ := h
  exact ⟨A, hA⟩

theorem HasBorelStrongSolver.toHasStrongSolver
    {p : ℕ} {gamma : ℝ} {b : ℕ}
    (h : HasBorelStrongSolver p gamma b) :
    HasStrongSolver p gamma b := by
  obtain ⟨S, hS, _⟩ := h
  exact ⟨S, hS⟩

theorem HasJointBorelResidualSolver.toHasBorelResidualSolver
    {p : ℕ} {alpha : ℝ} {b : ℕ}
    (h : HasJointBorelResidualSolver p alpha b) :
    HasBorelResidualSolver p alpha b := by
  obtain ⟨A, hA, hJoint⟩ := h
  exact ⟨A, hA, hJoint.isBorel⟩

theorem HasJointBorelStrongSolver.toHasBorelStrongSolver
    {p : ℕ} {gamma : ℝ} {b : ℕ}
    (h : HasJointBorelStrongSolver p gamma b) :
    HasBorelStrongSolver p gamma b := by
  obtain ⟨S, hS, hJoint⟩ := h
  exact ⟨S, hS, hJoint.isBorel⟩

theorem HasJointBorelResidualSolver.toHasResidualSolver
    {p : ℕ} {alpha : ℝ} {b : ℕ}
    (h : HasJointBorelResidualSolver p alpha b) :
    HasResidualSolver p alpha b :=
  h.toHasBorelResidualSolver.toHasResidualSolver

theorem HasJointBorelStrongSolver.toHasStrongSolver
    {p : ℕ} {gamma : ℝ} {b : ℕ}
    (h : HasJointBorelStrongSolver p gamma b) :
    HasStrongSolver p gamma b :=
  h.toHasBorelStrongSolver.toHasStrongSolver

/-- The same finite `p-1` hierarchy as `finite_upper_hierarchy`, now retaining
the full Borel outcome invariant at every edge. -/
theorem finite_upper_borel_hierarchy
    (p : ℕ) (hp : 2 ≤ p)
    (hbase : HasBorelStrongSolver p (hierarchyGamma p 0)
      (hierarchyStrongLogPower 0))
    (hboost : ∀ i, i ≤ p - 2 →
      HasBorelStrongSolver p (hierarchyGamma p i)
          (hierarchyStrongLogPower i) →
        HasBorelResidualSolver p (hierarchyGamma p (i + 1))
          (hierarchyResidualLogPower (i + 1)))
    (hrestart : ∀ j, 1 ≤ j → j ≤ p - 2 →
      HasBorelResidualSolver p (hierarchyGamma p j)
          (hierarchyResidualLogPower j) →
        HasBorelStrongSolver p (hierarchyGamma p j)
          (hierarchyStrongLogPower j)) :
    HasBorelResidualSolver p (2 / (3 * p - 1 : ℝ))
      (6 * (p - 1)) := by
  have hstrong : ∀ j, j ≤ p - 2 →
      HasBorelStrongSolver p (hierarchyGamma p j)
        (hierarchyStrongLogPower j) := by
    intro j hj
    induction j with
    | zero => exact hbase
    | succ j ih =>
        have hj' : j ≤ p - 2 := by omega
        exact hrestart (j + 1) (by omega) hj
          (hboost j hj' (ih hj'))
  have hlastStrong := hstrong (p - 2) le_rfl
  have hlastResidual := hboost (p - 2) le_rfl hlastStrong
  have hidx : p - 2 + 1 = p - 1 := by omega
  rw [hidx, hierarchyGamma_final (by omega : 1 ≤ p),
    hierarchyResidualLogPower_final] at hlastResidual
  exact hlastResidual

/-- Finite hierarchy with the joint, rather than merely pointwise, Borel
invariant.  This is the theorem used by the concrete final assembly. -/
theorem finite_upper_joint_borel_hierarchy
    (p : ℕ) (hp : 2 ≤ p)
    (hbase : HasJointBorelStrongSolver p (hierarchyGamma p 0)
      (hierarchyStrongLogPower 0))
    (hboost : ∀ i, i ≤ p - 2 →
      HasJointBorelStrongSolver p (hierarchyGamma p i)
          (hierarchyStrongLogPower i) →
        HasJointBorelResidualSolver p (hierarchyGamma p (i + 1))
          (hierarchyResidualLogPower (i + 1)))
    (hrestart : ∀ j, 1 ≤ j → j ≤ p - 2 →
      HasJointBorelResidualSolver p (hierarchyGamma p j)
          (hierarchyResidualLogPower j) →
        HasJointBorelStrongSolver p (hierarchyGamma p j)
          (hierarchyStrongLogPower j)) :
    HasJointBorelResidualSolver p (2 / (3 * p - 1 : ℝ))
      (6 * (p - 1)) := by
  have hstrong : ∀ j, j ≤ p - 2 →
      HasJointBorelStrongSolver p (hierarchyGamma p j)
        (hierarchyStrongLogPower j) := by
    intro j hj
    induction j with
    | zero => exact hbase
    | succ j ih =>
        have hj' : j ≤ p - 2 := by omega
        exact hrestart (j + 1) (by omega) hj
          (hboost j hj' (ih hj'))
  have hlastStrong := hstrong (p - 2) le_rfl
  have hlastResidual := hboost (p - 2) le_rfl hlastStrong
  have hidx : p - 2 + 1 = p - 1 := by omega
  rw [hidx, hierarchyGamma_final (by omega : 1 ≤ p),
    hierarchyResidualLogPower_final] at hlastResidual
  exact hlastResidual

section SourcePolicy

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A named proposition for the full frozen `def:policy` expansion.  The
existing `exact_policy_contract` theorem proves this for every value of the
policy structure; naming the proposition lets final upper-bound statements
expose that fact without repeating the expansion at every call site. -/
def FrozenExactPolicyContract (data : VIPublicData E) (epsilon : ℝ)
    (budget : ℕ)
    (policy : BorelStoppingPolicy (Answer := SymmetricExactJet E data.p)
      data.X budget) : Prop :=
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
        policy.IsPaddedRun oracle.answer seed history output)

theorem frozenExactPolicyContract_proof (data : VIPublicData E)
    (epsilon : ℝ) (budget : ℕ)
    (policy : BorelStoppingPolicy (Answer := SymmetricExactJet E data.p)
      data.X budget) :
    FrozenExactPolicyContract data epsilon budget policy := by
  exact exact_policy_contract data epsilon budget policy

/-- Agreement between one legacy capped execution and the source-facing
policy compiled from that exact call.  Both sides expose the same `used` and
the same returned certificate point; in particular there are no padding
queries in the operational witness. -/
def ResidualSolverFamily.CompiledPolicyAgrees
    {p : ℕ} (family : ResidualSolverFamily.{u} p)
    (hBorel : family.IsBorel) (alpha : ℝ) (b : ℕ)
    (data : VIPublicData E) (hp : data.p = p)
    (F : E → E) (hF : IsAdmissibleOperator data F)
    (center : data.X) (R epsilon : ℝ) : Prop :=
  let bcall := family.borelCall hBorel data hp center R epsilon
  let policy : BorelStoppingPolicy.{u, u, 0}
      (Answer := SymmetricExactJet E data.p) data.X bcall.call.cap :=
    bcall.toPolicy data
  FrozenExactPolicyContract data epsilon bcall.call.cap policy ∧
    policy.IsDeterministic ∧
    ∃ used : ℕ, ∃ cert : EvaluatedNormalCertificate data,
      ∃ hn : used ≤ bcall.call.cap,
        ∃ history : OracleHistory data.X
            (SymmetricExactJet E data.p) used,
          bcall.call.execute data F
              (hF.feasibleExactSymmetricJetOracle data F) =
                .finished used (some cert) ∧
          policy.RunSucceedsOnFeasible data F epsilon
            (hF.feasibleExactSymmetricJetOracle data F) center PUnit.unit
            used hn history cert.point ∧
          cert.IsVerifiedFor data F epsilon ∧
          (used : ℝ) ≤ residualInterfaceCost data family.leadingConstant
            alpha b R epsilon

/-- Source-facing witness that one concrete residual call and the compiled
policy have exactly the same successful output and number of genuine oracle
queries.  The policy itself depends only on public inputs; `F` occurs only in
the execution/success assertion. -/
theorem ResidualSolverFamily.borelPolicy_executes_same
    {p : ℕ} (family : ResidualSolverFamily.{u} p)
    (hBorel : family.IsBorel)
    (alpha : ℝ) (b : ℕ) (hinterface : family.SatisfiesInterface alpha b)
    (data : VIPublicData E) (hp : data.p = p)
    (F : E → E) (hF : IsAdmissibleOperator data F)
    (center : data.X) (R epsilon : ℝ)
    (hR : 0 < R) (hRD : R ≤ data.D) (hepsilon : 0 < epsilon)
    (zStar : E) (hz : IsVISolution data F zStar)
    (hdist : ‖center.1 - zStar‖ ≤ R) :
    family.CompiledPolicyAgrees hBorel alpha b data hp F hF center R epsilon := by
  unfold CompiledPolicyAgrees
  let bcall := family.borelCall hBorel data hp center R epsilon
  let policy := bcall.toPolicy data
  refine ⟨frozenExactPolicyContract_proof data epsilon bcall.call.cap policy,
    bcall.toPolicy_deterministic data, ?_⟩
  let oracle := hF.feasibleExactSymmetricJetOracle data F
  obtain ⟨used, cert, hrun, hcert, hcost⟩ :=
    (hinterface E data hp).2.2 F oracle center R epsilon hF hR hRD
      hepsilon zStar hz hdist
  have hrun' : bcall.call.execute data F oracle =
      .finished used (some cert) := by
    simpa [bcall, ResidualSolverFamily.borelCall] using hrun
  obtain ⟨hn, history, hpolicy⟩ :=
    bcall.toPolicy_runSucceedsOn_admissible data F hF epsilon hrun' hcert
  exact ⟨used, cert, hn, history, hrun', hpolicy, hcert, hcost⟩

/-- Fully expanded policy witness for a concrete successful family call.
The existential policy is definitionally the compiler output for the very
same capped call; the witness records the actual unpadded query count, not a
padded cost surrogate. -/
theorem ResidualSolverFamily.exists_compiledBorelPolicy
    {p : ℕ} (family : ResidualSolverFamily.{u} p)
    (hBorel : family.IsBorel)
    (alpha : ℝ) (b : ℕ) (hinterface : family.SatisfiesInterface alpha b)
    (data : VIPublicData E) (hp : data.p = p)
    (F : E → E) (hF : IsAdmissibleOperator data F)
    (center : data.X) (R epsilon : ℝ)
    (hR : 0 < R) (hRD : R ≤ data.D) (hepsilon : 0 < epsilon)
    (zStar : E) (hz : IsVISolution data F zStar)
    (hdist : ‖center.1 - zStar‖ ≤ R) :
    let call := (family.atData data hp).solve center R epsilon
    ∃ policy : BorelStoppingPolicy.{u, u, 0}
        (Answer := SymmetricExactJet E data.p) data.X call.cap,
      FrozenExactPolicyContract data epsilon call.cap policy ∧
      policy.IsDeterministic ∧
      (∀ state : policy.Seed × OracleHistory data.X
          (SymmetricExactJet E data.p) call.cap,
        ∃ output : data.X,
          policy.rule ⟨call.cap, Nat.lt_add_one call.cap⟩ state =
            Sum.inl output) ∧
      ∃ seed : policy.Seed, ∃ used : ℕ,
        ∃ cert : EvaluatedNormalCertificate data,
          ∃ hn : used ≤ call.cap,
            ∃ history : OracleHistory data.X
                (SymmetricExactJet E data.p) used,
              call.execute data F
                  (hF.feasibleExactSymmetricJetOracle data F) =
                    .finished used (some cert) ∧
              policy.RunSucceedsOnFeasible data F epsilon
                (hF.feasibleExactSymmetricJetOracle data F) center seed
                used hn history cert.point ∧
              cert.IsVerifiedFor data F epsilon ∧
              (used : ℝ) ≤ residualInterfaceCost data family.leadingConstant
                alpha b R epsilon := by
  let call := (family.atData data hp).solve center R epsilon
  let bcall := family.borelCall hBorel data hp center R epsilon
  let policy := bcall.toPolicy data
  have hagree := family.borelPolicy_executes_same hBorel alpha b hinterface
    data hp F hF center R epsilon hR hRD hepsilon zStar hz hdist
  change FrozenExactPolicyContract data epsilon bcall.call.cap policy ∧
      policy.IsDeterministic ∧
      ∃ used : ℕ, ∃ cert : EvaluatedNormalCertificate data,
        ∃ hn : used ≤ bcall.call.cap,
          ∃ history : OracleHistory data.X
              (SymmetricExactJet E data.p) used,
            bcall.call.execute data F
                (hF.feasibleExactSymmetricJetOracle data F) =
                  .finished used (some cert) ∧
            policy.RunSucceedsOnFeasible data F epsilon
              (hF.feasibleExactSymmetricJetOracle data F) center PUnit.unit
              used hn history cert.point ∧
            cert.IsVerifiedFor data F epsilon ∧
            (used : ℝ) ≤ residualInterfaceCost data family.leadingConstant
              alpha b R epsilon at hagree
  refine ⟨policy, hagree.1, hagree.2.1, policy.cap_stops, PUnit.unit, ?_⟩
  obtain ⟨used, cert, hn, history, hrun, hpolicy, hcert, hcost⟩ :=
    hagree.2.2
  exact ⟨used, cert, hn, history, hrun, hpolicy, hcert, hcost⟩

/-- Public-input-first form of the compiler theorem.  One policy is selected
before the unknown operator is quantified, and that same policy executes
successfully against the canonical exact feasible oracle of every admissible
operator satisfying the usual true-radius promise. -/
theorem ResidualSolverFamily.exists_uniformCompiledBorelPolicy
    {p : ℕ} (family : ResidualSolverFamily.{u} p)
    (hBorel : family.IsBorel)
    (alpha : ℝ) (b : ℕ) (hinterface : family.SatisfiesInterface alpha b)
    (data : VIPublicData E) (hp : data.p = p)
    (center : data.X) (R epsilon : ℝ) :
    let call := (family.atData data hp).solve center R epsilon
    ∃ policy : BorelStoppingPolicy.{u, u, 0}
        (Answer := SymmetricExactJet E data.p) data.X call.cap,
      FrozenExactPolicyContract data epsilon call.cap policy ∧
      policy.IsDeterministic ∧
      (∀ state : policy.Seed × OracleHistory data.X
          (SymmetricExactJet E data.p) call.cap,
        ∃ output : data.X,
          policy.rule ⟨call.cap, Nat.lt_add_one call.cap⟩ state =
            Sum.inl output) ∧
      ∀ (F : E → E) (hF : IsAdmissibleOperator data F),
        0 < R → R ≤ data.D → 0 < epsilon →
        ∀ zStar, IsVISolution data F zStar → ‖center.1 - zStar‖ ≤ R →
          ∃ seed : policy.Seed, ∃ used : ℕ,
            ∃ cert : EvaluatedNormalCertificate data,
              ∃ hn : used ≤ call.cap,
                ∃ history : OracleHistory data.X
                    (SymmetricExactJet E data.p) used,
                  call.execute data F
                      (hF.feasibleExactSymmetricJetOracle data F) =
                        .finished used (some cert) ∧
                  policy.RunSucceedsOnFeasible data F epsilon
                    (hF.feasibleExactSymmetricJetOracle data F)
                    center seed used hn history cert.point ∧
                  cert.IsVerifiedFor data F epsilon ∧
                  (used : ℝ) ≤ residualInterfaceCost data
                    family.leadingConstant alpha b R epsilon := by
  let call := (family.atData data hp).solve center R epsilon
  let bcall := family.borelCall hBorel data hp center R epsilon
  let policy := bcall.toPolicy data
  refine ⟨policy, frozenExactPolicyContract_proof data epsilon
    bcall.call.cap policy, bcall.toPolicy_deterministic data,
    policy.cap_stops, ?_⟩
  intro F hF hR hRD hepsilon zStar hz hdist
  have hagree := family.borelPolicy_executes_same hBorel alpha b hinterface
    data hp F hF center R epsilon hR hRD hepsilon zStar hz hdist
  change FrozenExactPolicyContract data epsilon bcall.call.cap policy ∧
      policy.IsDeterministic ∧
      ∃ used : ℕ, ∃ cert : EvaluatedNormalCertificate data,
        ∃ hn : used ≤ bcall.call.cap,
          ∃ history : OracleHistory data.X
              (SymmetricExactJet E data.p) used,
            bcall.call.execute data F
                (hF.feasibleExactSymmetricJetOracle data F) =
                  .finished used (some cert) ∧
            policy.RunSucceedsOnFeasible data F epsilon
              (hF.feasibleExactSymmetricJetOracle data F) center PUnit.unit
              used hn history cert.point ∧
            cert.IsVerifiedFor data F epsilon ∧
            (used : ℝ) ≤ residualInterfaceCost data family.leadingConstant
              alpha b R epsilon at hagree
  obtain ⟨used, cert, hn, history, hrun, hpolicy, hcert, hcost⟩ :=
    hagree.2.2
  exact ⟨PUnit.unit, used, cert, hn, history, hrun, hpolicy, hcert, hcost⟩

end SourcePolicy

section FinalSourceClaim

/-- Strengthened upper half of `thm:main`: the final family has the numerical
interface and every promised successful call is witnessed by a genuine
singleton-seed `BorelStoppingPolicy` satisfying the full frozen
`def:policy` contract. -/
def BorelDistanceSensitiveUpperClaim (p : ℕ) : Prop :=
  ∃ A : ResidualSolverFamily.{0} p,
    ∃ hBorel : A.HasJointBorelCappedOutcome,
      A.SatisfiesInterface (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hp : data.p = p)
        (center : data.X) (R epsilon : ℝ),
        let call := (A.atData data hp).solve center R epsilon
        ∃ policy : BorelStoppingPolicy.{0, 0, 0}
            (Answer := SymmetricExactJet E data.p) data.X call.cap,
          FrozenExactPolicyContract data epsilon call.cap policy ∧
          policy.IsDeterministic ∧
          (∀ state : policy.Seed × OracleHistory data.X
              (SymmetricExactJet E data.p) call.cap,
            ∃ output : data.X,
              policy.rule ⟨call.cap, Nat.lt_add_one call.cap⟩ state =
                Sum.inl output) ∧
          ∀ (F : E → E) (hF : IsAdmissibleOperator data F),
            0 < R → R ≤ data.D → 0 < epsilon →
            ∀ zStar, IsVISolution data F zStar →
              ‖center.1 - zStar‖ ≤ R →
              ∃ seed : policy.Seed, ∃ used : ℕ,
                ∃ cert : EvaluatedNormalCertificate data,
                  ∃ hn : used ≤ call.cap,
                    ∃ history : OracleHistory data.X
                        (SymmetricExactJet E data.p) used,
                      call.execute data F
                          (hF.feasibleExactSymmetricJetOracle data F) =
                            .finished used (some cert) ∧
                      policy.RunSucceedsOnFeasible data F epsilon
                        (hF.feasibleExactSymmetricJetOracle data F)
                        center seed used hn history cert.point ∧
                      cert.IsVerifiedFor data F epsilon ∧
                      (used : ℝ) ≤ residualInterfaceCost data
                        A.leadingConstant (2 / (3 * p - 1 : ℝ))
                        (6 * (p - 1)) R epsilon

theorem borelDistanceSensitiveUpperClaim_of_solver
    (p : ℕ)
    (hsolver : HasJointBorelResidualSolver p
      (2 / (3 * p - 1 : ℝ)) (6 * (p - 1))) :
    BorelDistanceSensitiveUpperClaim p := by
  obtain ⟨A, hinterface, hBorel⟩ := hsolver
  refine ⟨A, hBorel, hinterface, ?_⟩
  intro E _ _ _ _ _ data hp center R epsilon
  exact A.exists_uniformCompiledBorelPolicy hBorel.isBorel
    (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) hinterface
    data hp center R epsilon

/-- Universal source-facing Borel upper package. -/
def MainBorelUpperClaim : Prop :=
  ∀ p, 2 ≤ p → BorelDistanceSensitiveUpperClaim p

/-- One proposition tying the already proved matching lower/upper numerical
package to the actual source-policy implementation of its upper family. -/
def MainBorelSourceContract : Prop :=
  MainTheoremClaim ∧ MainBorelUpperClaim

theorem mainBorelUpperClaim_of_transformations
    (hbase : ∀ p, 2 ≤ p →
      HasJointBorelStrongSolver p (hierarchyGamma p 0)
        (hierarchyStrongLogPower 0))
    (hboost : ∀ p, 2 ≤ p → ∀ i, i ≤ p - 2 →
      HasJointBorelStrongSolver p (hierarchyGamma p i)
          (hierarchyStrongLogPower i) →
        HasJointBorelResidualSolver p (hierarchyGamma p (i + 1))
          (hierarchyResidualLogPower (i + 1)))
    (hrestart : ∀ p, 2 ≤ p → ∀ j, 1 ≤ j → j ≤ p - 2 →
      HasJointBorelResidualSolver p (hierarchyGamma p j)
          (hierarchyResidualLogPower j) →
        HasJointBorelStrongSolver p (hierarchyGamma p j)
          (hierarchyStrongLogPower j)) :
    MainBorelUpperClaim := by
  intro p hp
  exact borelDistanceSensitiveUpperClaim_of_solver p
    (finite_upper_joint_borel_hierarchy p hp (hbase p hp)
      (hboost p hp) (hrestart p hp))

/-- Assembly theorem for the numerical main claim and the Borel-policy claim
from one and the same hierarchy invariant. -/
theorem mainBorelSourceContract_of_transformations
    (hbase : ∀ p, 2 ≤ p →
      HasJointBorelStrongSolver p (hierarchyGamma p 0)
        (hierarchyStrongLogPower 0))
    (hboost : ∀ p, 2 ≤ p → ∀ i, i ≤ p - 2 →
      HasJointBorelStrongSolver p (hierarchyGamma p i)
          (hierarchyStrongLogPower i) →
        HasJointBorelResidualSolver p (hierarchyGamma p (i + 1))
          (hierarchyResidualLogPower (i + 1)))
    (hrestart : ∀ p, 2 ≤ p → ∀ j, 1 ≤ j → j ≤ p - 2 →
      HasJointBorelResidualSolver p (hierarchyGamma p j)
          (hierarchyResidualLogPower j) →
        HasJointBorelStrongSolver p (hierarchyGamma p j)
          (hierarchyStrongLogPower j)) :
    MainBorelSourceContract := by
  refine ⟨?_, mainBorelUpperClaim_of_transformations hbase hboost hrestart⟩
  refine ⟨lowerBoundClosureClaim_proof, mainRandomLowerClosureClaim_proof, ?_⟩
  intro p hp
  have hsolver := finite_upper_joint_borel_hierarchy p hp (hbase p hp)
    (hboost p hp) (hrestart p hp)
  have hplain := hsolver.toHasResidualSolver
  exact ⟨upperDiameterBoundClaim_of_solver p hplain,
    distanceSensitiveUpperClaim_of_solver p hplain⟩

end FinalSourceClaim

end

end LeanArticleAudit.Pilot
