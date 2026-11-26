import LeanArticleAudit.Pilot.UpperRestartClaim
import LeanArticleAudit.Pilot.UpperBorelRestart

/-! Direct source-facing expansion of `lem:restart`. -/

namespace LeanArticleAudit.Pilot

noncomputable section

universe u

/-- The concrete certified restart family, with both semantic clauses and the
input/output installed-cap Borel observables expanded to measurable replay in
the theorem statement. -/
theorem restart_source_contract
    (p : ℕ) (A : ResidualSolverFamily.{u} p) (alpha : ℝ) (b : ℕ)
    (hA : A.SatisfiesInterface alpha b)
    (hAordinary :
      ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ),
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun z : data.X ×
          (Fin n → data.X × SymmetricExactJet E data.p) =>
        ExactJetProgram.replayOutcomeAction
          (((A.atData data hp).solve z.1 R epsilon).installedProgram data)
          z.2))
    (hAanchored :
      ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ),
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun z : (data.X × data.X) ×
          (Fin n → data.X × SymmetricExactJet E data.p) =>
        let shifted := data.withStart z.1.1
        let call := (A.atData shifted hp).solve z.1.2 R epsilon
        ExactJetProgram.replayOutcomeAction
          (call.anchoredInstalledProgram data z.1.1) z.2))
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p),
      let S := (certifiedRestartFamily p A alpha b).atData data hp
      (∀ (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
        center mu delta used cert, IsAdmissibleOperator data G →
        0 < mu → 0 < delta →
        (S.solve center mu delta).execute data G oracle =
          .finished used (some cert) → cert.IsVerifiedFor data G delta) ∧
      (∀ (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
        center mu delta, IsAdmissibleOperator data G →
        0 < mu → 0 < delta → StronglyMonotoneOn data G mu →
        ∀ zStar, IsVISolution data G zStar →
          ∃ used cert,
            (S.solve center mu delta).execute data G oracle =
              .finished used (some cert) ∧
            cert.IsVerifiedFor data G delta ∧
            (used : ℝ) ≤ strongInterfaceCost data S.leadingConstant alpha
              (b + 2) ‖center.1 - zStar‖ mu delta)) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ),
      let S := certifiedRestartFamily p A alpha b
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun z : data.X ×
          (Fin n → data.X × SymmetricExactJet E data.p) =>
        ExactJetProgram.replayOutcomeAction
          (((S.atData data hp).solve z.1 mu delta).installedProgram data)
          z.2)) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ),
      let S := certifiedRestartFamily p A alpha b
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun z : (data.X × data.X) ×
          (Fin n → data.X × SymmetricExactJet E data.p) =>
        let shifted := data.withStart z.1.1
        let call := (S.atData shifted hp).solve z.1.2 mu delta
        ExactJetProgram.replayOutcomeAction
          (call.anchoredInstalledProgram data z.1.1) z.2)) := by
  have hS := certifiedRestartFamily_satisfies p A alpha b hA halpha0 halpha1
  have hABorel : A.HasJointBorelCappedOutcome := by
    constructor
    · intro E _ _ _ _ _ data hp R epsilon
      exact hAordinary E data hp R epsilon
    · intro E _ _ _ _ _ data hp R epsilon
      exact hAanchored E data hp R epsilon
  have hSBorel := certifiedRestartFamily_hasJointBorelCappedOutcome
    A hABorel alpha b
  refine ⟨?_, ?_, ?_⟩
  · intro E _ _ _ data hp
    exact hS E data hp
  · intro E _ _ _ _ _ data hp mu delta
    exact hSBorel.ordinary data hp mu delta
  · intro E _ _ _ _ _ data hp mu delta
    exact hSBorel.anchored data hp mu delta

end

end LeanArticleAudit.Pilot
