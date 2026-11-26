import LeanArticleAudit.Pilot.LowerBudgetClosure
import LeanArticleAudit.Pilot.UpperHierarchy

/-!
# Assembly bridge for the matching theorem

This module deliberately separates the finite algorithmic construction from
the final theorem.  It proves that a genuine base solver and the two genuine
solver transformations produce the exact terminal exponent/logarithmic power,
while retaining the already closed deterministic, randomized, and zero-query
lower package.
-/

namespace LeanArticleAudit.Pilot

noncomputable section

/-- Explicit diameter-only upper half of `thm:main`.  This spells out the
actual capped call, evaluated certificate, and dimension-free numerical bound
instead of leaving them behind an asymptotic notation. -/
def UpperDiameterBoundClaim (p : ℕ) : Prop :=
  ∃ A : ResidualSolverFamily.{0} p,
    A.SatisfiesInterface (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p)
      (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F),
      IsAdmissibleOperator data F →
      ∀ epsilon, 0 < epsilon → ∀ zStar, IsVISolution data F zStar →
        ∃ used cert,
          ((A.atData data hp).solve ⟨data.x0, data.x0_mem⟩ data.D epsilon).execute
              data F oracle =
                CappedRunResult.finished used (some cert) ∧
          cert.IsVerifiedFor data F epsilon ∧
          (used : ℝ) ≤ A.leadingConstant *
            (1 + (data.Lp * data.D ^ data.p / epsilon) ^
              (2 / (3 * data.p - 1 : ℝ))) *
            (1 + Real.log
              (3 + data.Lp * data.D ^ data.p / epsilon)) ^
                (6 * (data.p - 1))

/-- The stronger distance-sensitive corollary, including safe behavior when
the supplied distance promise is false. -/
def DistanceSensitiveUpperClaim (p : ℕ) : Prop :=
  ∃ A : ResidualSolverFamily.{0} p,
    A.SatisfiesInterface (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) ∧
    (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p)
      (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
      (center : data.X) (R epsilon : ℝ),
      IsAdmissibleOperator data F → 0 < R → R ≤ data.D → 0 < epsilon →
      ∀ zStar, IsVISolution data F zStar → ‖center.1 - zStar‖ ≤ R →
        ∃ used cert,
          ((A.atData data hp).solve center R epsilon).execute data F oracle =
            CappedRunResult.finished used (some cert) ∧
          cert.IsVerifiedFor data F epsilon ∧
          (used : ℝ) ≤ residualInterfaceCost data A.leadingConstant
            (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) R epsilon) ∧
    (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p)
      (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
      (hF : IsAdmissibleOperator data F)
      (center : data.X) (R epsilon : ℝ) used cert,
      0 < R → 0 < epsilon →
      ((A.atData data hp).solve center R epsilon).execute data F oracle =
          CappedRunResult.finished used (some cert) →
        cert.IsVerifiedFor data F epsilon)

/-- The operational core of the main theorem at a fixed order.  The residual
solver is a single dimension-independent family with a positive leading
constant; its interface returns evaluated tangent-residual certificates and
enforces a cap on actual oracle calls. -/
def MainOperationalClaim (p : ℕ) : Prop :=
  LowerBoundClosureClaim ∧
    MainRandomLowerClosureClaim ∧
    UpperDiameterBoundClaim p

/-- Full source-facing assembly target.  The lower package includes the two
high-dimensional regimes, the zero-query boundary, and
`T_rand ≤ T_det`; the upper package includes both the displayed diameter
bound and its stronger distance-sensitive form. -/
def MainTheoremClaim : Prop :=
  LowerBoundClosureClaim ∧
    MainRandomLowerClosureClaim ∧
    ∀ p, 2 ≤ p → UpperDiameterBoundClaim p ∧
      DistanceSensitiveUpperClaim p

theorem upperDiameterBoundClaim_of_solver
    (p : ℕ)
    (hsolver : HasResidualSolver p
      (2 / (3 * p - 1 : ℝ)) (6 * (p - 1))) :
    UpperDiameterBoundClaim p := by
  obtain ⟨A, hA⟩ := hsolver
  refine ⟨A, hA, ?_⟩
  intro E _ _ _ data hp F oracle hF epsilon hepsilon zStar hz
  have hdist : ‖data.x0 - zStar‖ ≤ data.D := by
    rw [← dist_eq_norm]
    exact data.diameter_le data.x0 data.x0_mem zStar hz.1
  obtain ⟨used, cert, hrun, hcert, hcost⟩ :=
    (hA E data hp).2.2 F oracle ⟨data.x0, data.x0_mem⟩
      data.D epsilon hF data.D_pos le_rfl hepsilon zStar hz hdist
  refine ⟨used, cert, hrun, hcert, ?_⟩
  rw [residualInterfaceCost_at_diameter] at hcost
  simpa [hp, ResidualSolverFamily.atData] using hcost

theorem distanceSensitiveUpperClaim_of_solver
    (p : ℕ)
    (hsolver : HasResidualSolver p
      (2 / (3 * p - 1 : ℝ)) (6 * (p - 1))) :
    DistanceSensitiveUpperClaim p := by
  obtain ⟨A, hA⟩ := hsolver
  refine ⟨A, hA, ?_, ?_⟩
  · intro E _ _ _ data hp F oracle center R epsilon hF hR hRD
      hepsilon zStar hz hdist
    exact (hA E data hp).2.2 F oracle center R epsilon hF hR hRD
      hepsilon zStar hz hdist
  · intro E _ _ _ data hp F oracle hF center R epsilon used cert hR hepsilon hrun
    exact (hA E data hp).2.1 F oracle center R epsilon used cert hF hR hepsilon hrun

/-- Once the three executable ingredients have been proved, the main
operational statement follows by a finite `p-1`-level construction. -/
theorem mainOperationalClaim_of_transformations
    (p : ℕ) (hp : 2 ≤ p)
    (hbase : HasStrongSolver p (hierarchyGamma p 0)
      (hierarchyStrongLogPower 0))
    (hboost : ∀ i, i ≤ p - 2 →
      HasStrongSolver p (hierarchyGamma p i) (hierarchyStrongLogPower i) →
      HasResidualSolver p (hierarchyGamma p (i + 1))
        (hierarchyResidualLogPower (i + 1)))
    (hrestart : ∀ j, 1 ≤ j → j ≤ p - 2 →
      HasResidualSolver p (hierarchyGamma p j) (hierarchyResidualLogPower j) →
      HasStrongSolver p (hierarchyGamma p j) (hierarchyStrongLogPower j)) :
    MainOperationalClaim p := by
  exact ⟨lowerBoundClosureClaim_proof, mainRandomLowerClosureClaim_proof,
    upperDiameterBoundClaim_of_solver p
      (finite_upper_hierarchy p hp hbase hboost hrestart)⟩

/-- Universal version of the assembly bridge.  The hypotheses are exactly
the three executable constructions still proved in separate modules. -/
theorem mainTheoremClaim_of_transformations
    (hbase : ∀ p, 2 ≤ p →
      HasStrongSolver p (hierarchyGamma p 0) (hierarchyStrongLogPower 0))
    (hboost : ∀ p, 2 ≤ p → ∀ i, i ≤ p - 2 →
      HasStrongSolver p (hierarchyGamma p i) (hierarchyStrongLogPower i) →
      HasResidualSolver p (hierarchyGamma p (i + 1))
        (hierarchyResidualLogPower (i + 1)))
    (hrestart : ∀ p, 2 ≤ p → ∀ j, 1 ≤ j → j ≤ p - 2 →
      HasResidualSolver p (hierarchyGamma p j) (hierarchyResidualLogPower j) →
      HasStrongSolver p (hierarchyGamma p j) (hierarchyStrongLogPower j)) :
    MainTheoremClaim := by
  refine ⟨lowerBoundClosureClaim_proof, mainRandomLowerClosureClaim_proof, ?_⟩
  intro p hp
  let hsolver := finite_upper_hierarchy p hp (hbase p hp)
    (hboost p hp) (hrestart p hp)
  exact ⟨upperDiameterBoundClaim_of_solver p hsolver,
    distanceSensitiveUpperClaim_of_solver p hsolver⟩

/-- Diameter substitution giving exactly the displayed upper expression in
`thm:main`; in particular no dimension occurs in the bound. -/
theorem main_diameter_cost_identity
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (data : VIPublicData E) (C epsilon : ℝ) :
    residualInterfaceCost data C (2 / (3 * data.p - 1 : ℝ))
        (6 * (data.p - 1)) data.D epsilon =
      C * (1 + (data.Lp * data.D ^ data.p / epsilon) ^
          (2 / (3 * data.p - 1 : ℝ))) *
        (1 + Real.log
          (3 + data.Lp * data.D ^ data.p / epsilon)) ^
            (6 * (data.p - 1)) := by
  exact residualInterfaceCost_at_diameter data C
    (2 / (3 * data.p - 1 : ℝ)) (6 * (data.p - 1)) epsilon

end

end LeanArticleAudit.Pilot
