import LeanArticleAudit.Pilot.UpperFinalAssembly
import LeanArticleAudit.Pilot.UpperBorelComplexity
import LeanArticleAudit.Pilot.UpperBorelFinalAssembly
import LeanArticleAudit.Pilot.BorelLowerClosure

/-! Direct, source-facing statements for the final corollary and theorem. -/

open Set MeasureTheory

namespace LeanArticleAudit.Pilot

noncomputable section

/-- `corollary-L1135`, with the residual-family contract expanded in the
statement rather than hidden behind a named proposition. -/
theorem corollary_L1135_proof :
    ∀ p, 2 ≤ p → ∃ A : ResidualSolverFamily.{0} p,
      A.SatisfiesInterface (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p)
        (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
        (center : data.X) (R epsilon : ℝ),
        IsAdmissibleOperator data F → 0 < R → R ≤ data.D → 0 < epsilon →
        ∀ zStar, IsVISolution data F zStar → ‖center.1 - zStar‖ ≤ R →
          ∃ used cert,
            ((A.atData data hp).solve center R epsilon).execute data F oracle =
              .finished used (some cert) ∧
            cert.IsVerifiedFor data F epsilon ∧
            (used : ℝ) ≤ residualInterfaceCost data A.leadingConstant
              (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) R epsilon) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p)
        (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
        (center : data.X) (R epsilon : ℝ) used cert,
        IsAdmissibleOperator data F → 0 < R → 0 < epsilon →
        ((A.atData data hp).solve center R epsilon).execute data F oracle =
          .finished used (some cert) → cert.IsVerifiedFor data F epsilon) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hpData : data.p = p)
        (center : data.X) (R epsilon : ℝ),
        let call := (A.atData data hpData).solve center R epsilon
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
                        (6 * (p - 1)) R epsilon) := by
  intro p hp
  obtain ⟨A, hA, hBorel⟩ := final_upper_joint_borel_hierarchy p hp
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · intro E _ _ _ data hpData F oracle center R epsilon hF hR hRD
      hepsilon zStar hz hdist
    exact (hA E data hpData).2.2 F oracle center R epsilon hF hR hRD
      hepsilon zStar hz hdist
  · intro E _ _ _ data hpData F oracle center R epsilon used cert hF hR
      hepsilon hrun
    exact (hA E data hpData).2.1 F oracle center R epsilon used cert hF hR
      hepsilon hrun
  · intro E _ _ _ _ _ data hpData center R epsilon
    exact A.exists_uniformCompiledBorelPolicy hBorel.isBorel
      (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) hA
      data hpData center R epsilon

/-- Direct operational content of `thm:main`.  The same positive `c_p` is
used for every budget, and the same final capped residual family supplies the
diameter and distance-sensitive upper bounds in every finite dimension. -/
theorem thm_main_proof :
    ∀ p, ∀ hp : 2 ≤ p,
    ∃ (c_p : ℝ) (A : ResidualSolverFamily.{0} p),
      c_p = sourceMainLowerConstant p ∧ 0 < c_p ∧
      A.SatisfiesInterface (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) ∧
      (∀ (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
        (hD : D = 2 * R) (hepsilon : 0 < epsilon) (N : ℕ),
        (N : ℝ) < c_p *
          deterministicConditionNumber p Lp D epsilon ^
            deterministicRateExponent p →
        UnifiedRandomBudgetObstruction p hp Lp R D epsilon
          hLp hR hD hepsilon N) ∧
      (∀ (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
        (hD : D = 2 * R) (hepsilon : 0 < epsilon),
        2 ≤ deterministicConditionNumber p Lp D epsilon → ∀ N,
        ((N = 0 → ∃ policy : BorelStoppingPolicy.{0, 0, 0}
            (Answer := ZeroQueryAnswer p)
            (intervalVIData p hp Lp D hLp
              (hD.symm ▸ by positivity)).X 0,
              ZeroQueryUniformSuccess p hp Lp D epsilon hLp
                (hD.symm ▸ by positivity) policy) ∧
          (1 ≤ N → ∀ (d : ℕ) [NeZero d],
            RandomDimensionCondition N d (1 / 4 : ℝ) →
            ∃ policy : BorelStoppingPolicy.{0, 0, 0}
                (Answer := SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
                (ballVIData (E := EuclideanSpace ℝ (Fin d))
                  p hp Lp hLp R hR).X N,
              BorelRandomUniformSuccess
                (ballVIData (E := EuclideanSpace ℝ (Fin d))
                  p hp Lp hLp R hR) N policy epsilon)) →
        c_p * deterministicConditionNumber p Lp D epsilon ^
          deterministicRateExponent p ≤ (N : ℝ)) ∧
      (∀ (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
        (hD : D = 2 * R) (hepsilon : 0 < epsilon),
        2 ≤ deterministicConditionNumber p Lp D epsilon → ∀ N,
        ((N = 0 → ∃ policy : BorelStoppingPolicy.{0, 0, 0}
            (Answer := ZeroQueryAnswer p)
            (intervalVIData p hp Lp D hLp
              (hD.symm ▸ by positivity)).X 0,
              policy.IsDeterministic ∧
              ZeroQueryUniformSuccess p hp Lp D epsilon hLp
                (hD.symm ▸ by positivity) policy) ∧
          (1 ≤ N → ∀ (d : ℕ) [NeZero d],
            RandomDimensionCondition N d (1 / 4 : ℝ) →
            ∃ policy : BorelStoppingPolicy.{0, 0, 0}
                (Answer := SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
                (ballVIData (E := EuclideanSpace ℝ (Fin d))
                  p hp Lp hLp R hR).X N,
              BorelDeterministicUniformSuccess
                (ballVIData (E := EuclideanSpace ℝ (Fin d))
                  p hp Lp hLp R hR) N policy epsilon)) →
        c_p * deterministicConditionNumber p Lp D epsilon ^
          deterministicRateExponent p ≤ (N : ℝ)) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [Nontrivial E]
        (Lp R : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
        (N : ℕ) (hN : 1 ≤ N)
        (hdim : 2 * N + 2 ≤ Module.finrank ℝ E)
        (policy : DeterministicPolicy (Metric.closedBall (0 : E) R)
          (ExactJet E p) N),
        ∃ v : Fin (N + 1) → E,
          Orthonormal ℝ v ∧
          IsAdmissibleOperator (ballVIData (E := E) p hp Lp hLp R hR)
            (hiddenOperator p standardGateProfile Lp R N v) ∧
          hiddenResidualClosedForm p standardGateProfile Lp R N ≤
            tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
              (hiddenOperator p standardGateProfile Lp R N v)
              (policy.run (exactJet p
                (hiddenOperator p standardGateProfile Lp R N v))).1) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (budget : ℕ) (epsilon : ℝ),
        BorelDeterministicBudgetSurvives data budget epsilon →
          BorelRandomBudgetSurvives data budget epsilon) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (data : VIPublicData E) (hpData : data.p = p)
        (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F),
        IsAdmissibleOperator data F → ∀ epsilon, 0 < epsilon →
        ∀ zStar, IsVISolution data F zStar →
          ∃ used cert,
            ((A.atData data hpData).solve ⟨data.x0, data.x0_mem⟩ data.D epsilon).execute
                data F oracle = .finished used (some cert) ∧
            cert.IsVerifiedFor data F epsilon ∧
            (used : ℝ) ≤ A.leadingConstant *
              (1 + (data.Lp * data.D ^ data.p / epsilon) ^
                (2 / (3 * data.p - 1 : ℝ))) *
              (1 + Real.log (3 + data.Lp * data.D ^ data.p / epsilon)) ^
                (6 * (data.p - 1))) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (data : VIPublicData E) (hpData : data.p = p)
        (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
        (center : data.X) (R epsilon : ℝ),
        IsAdmissibleOperator data F → 0 < R → R ≤ data.D → 0 < epsilon →
        ∀ zStar, IsVISolution data F zStar → ‖center.1 - zStar‖ ≤ R →
          ∃ used cert,
            ((A.atData data hpData).solve center R epsilon).execute data F oracle =
              .finished used (some cert) ∧
            cert.IsVerifiedFor data F epsilon ∧
            (used : ℝ) ≤ residualInterfaceCost data A.leadingConstant
              (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) R epsilon) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (data : VIPublicData E) (hpData : data.p = p)
        (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
        (center : data.X) (R epsilon : ℝ) used cert,
        IsAdmissibleOperator data F → 0 < R → 0 < epsilon →
        ((A.atData data hpData).solve center R epsilon).execute data F oracle =
          .finished used (some cert) → cert.IsVerifiedFor data F epsilon) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hpData : data.p = p)
        (center : data.X) (R epsilon : ℝ),
        let call := (A.atData data hpData).solve center R epsilon
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
                        (6 * (p - 1)) R epsilon) := by
  intro p hp
  obtain ⟨A, hA, hBorel⟩ := final_upper_joint_borel_hierarchy p hp
  refine ⟨sourceMainLowerConstant p, A, rfl,
    sourceMainLowerConstant_pos p hp, hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Lp R D epsilon hLp hR hD hepsilon N hbudget
    exact unifiedRandomBudgetObstruction p hp Lp R D epsilon hLp hR hD
      hepsilon N hbudget
  · intro Lp R D epsilon hLp hR hD hepsilon hQ N hsuccess
    apply sourceBorelRandomSuccessfulBudget_lower p hp Lp R D epsilon hLp hR
      hD hepsilon hQ N
    change SourceBorelRandomBudgetSuccess p hp Lp R D epsilon
      hLp hR hD N at hsuccess
    exact hsuccess
  · intro Lp R D epsilon hLp hR hD hepsilon hQ N hsuccess
    apply sourceBorelDeterministicSuccessfulBudget_lower p hp Lp R D epsilon
      hLp hR hD hepsilon hQ N
    change SourceBorelDeterministicBudgetSuccess p hp Lp R D epsilon
      hLp hR hD N at hsuccess
    exact hsuccess
  · intro E _ _ _ _ Lp R hLp hR N hN hdim policy
    exact deterministicLowerClaim_proof E p hp standardGateProfile Lp R hLp hR
      N hN N le_rfl hdim policy
  · intro E _ _ _ _ _ data budget epsilon hsuccess
    exact borelRandomBudgetSurvives_of_deterministic data budget epsilon hsuccess
  · intro E _ _ _ data hpData F oracle hF epsilon hepsilon zStar hz
    have hdist : ‖data.x0 - zStar‖ ≤ data.D := by
      rw [← dist_eq_norm]
      exact data.diameter_le data.x0 data.x0_mem zStar hz.1
    obtain ⟨used, cert, hrun, hcert, hcost⟩ :=
      (hA E data hpData).2.2 F oracle ⟨data.x0, data.x0_mem⟩ data.D epsilon
        hF data.D_pos le_rfl hepsilon zStar hz hdist
    refine ⟨used, cert, hrun, hcert, ?_⟩
    rw [residualInterfaceCost_at_diameter] at hcost
    simpa [hpData, ResidualSolverFamily.atData] using hcost
  · intro E _ _ _ data hpData F oracle center R epsilon hF hR hRD hepsilon
      zStar hz hdist
    exact (hA E data hpData).2.2 F oracle center R epsilon hF hR hRD hepsilon
      zStar hz hdist
  · intro E _ _ _ data hpData F oracle center R epsilon used cert hF hR
      hepsilon hrun
    exact (hA E data hpData).2.1 F oracle center R epsilon used cert hF hR
      hepsilon hrun
  · intro E _ _ _ _ _ data hpData center R epsilon
    exact A.exists_uniformCompiledBorelPolicy hBorel.isBorel
      (2 / (3 * p - 1 : ℝ)) (6 * (p - 1)) hA
      data hpData center R epsilon

end

end LeanArticleAudit.Pilot
