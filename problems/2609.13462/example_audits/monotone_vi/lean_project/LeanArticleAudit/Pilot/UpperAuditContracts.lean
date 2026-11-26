import LeanArticleAudit.Pilot.ApproxRecoveryClaim
import LeanArticleAudit.Pilot.ModelMeasurableSelector
import LeanArticleAudit.Pilot.ZeroQuery
import LeanArticleAudit.Pilot.UpperBaseStrongClaim
import LeanArticleAudit.Pilot.UpperBorelBase
import LeanArticleAudit.Pilot.UpperBorelBoostRestart
import LeanArticleAudit.Pilot.UpperBoostTransformation
import LeanArticleAudit.Pilot.MainAssembly

/-!
# Expanded source-facing contracts for the stable upper-chain slots

Unlike wrapper headlines of the form `proof : NamedClaim`, every theorem in
this file places the source-relevant quantifiers and conclusions directly in
its signature so that the statement-hash gate binds the mathematical content.
-/

open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace LeanArticleAudit.Pilot

noncomputable section

universe u

section Interfaces

/-- Fully expanded, hash-binding definition contract for `def:interfaces`.
Besides the semantic residual/strong clauses, the final two equivalences
expand the compositional Borel requirement down to measurable replay of the
actual installed cap, both at a fixed public anchor and jointly in a changed
anchor and solve center. -/
theorem interfaces_source_contract :
    ∀ (p : ℕ),
      (∀ (A : ResidualSolverFamily.{u} p) (alpha : ℝ) (b : ℕ),
        A.SatisfiesInterface alpha b ↔
          ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
            [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p),
            (∀ center R epsilon,
              0 < R → R ≤ data.D → 0 < epsilon →
                ((((A.atData data hp).solve center R epsilon).cap : ℕ) : ℝ) ≤
                  residualInterfaceCost data A.leadingConstant alpha b R epsilon) ∧
            (∀ (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
                center R epsilon used cert, IsAdmissibleOperator data F →
              0 < R → 0 < epsilon →
              ((A.atData data hp).solve center R epsilon).execute data F oracle =
                  .finished used (some cert) →
                cert.IsVerifiedFor data F epsilon) ∧
            (∀ (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
                center R epsilon, IsAdmissibleOperator data F →
              0 < R → R ≤ data.D → 0 < epsilon →
              ∀ zStar, IsVISolution data F zStar → ‖center.1 - zStar‖ ≤ R →
                ∃ used cert,
                  ((A.atData data hp).solve center R epsilon).execute data F oracle =
                    .finished used (some cert) ∧
                  cert.IsVerifiedFor data F epsilon ∧
                  (used : ℝ) ≤ residualInterfaceCost data A.leadingConstant
                    alpha b R epsilon)) ∧
      (∀ (S : StrongSolverFamily.{u} p) (gamma : ℝ) (b : ℕ),
        S.SatisfiesInterface gamma b ↔
          ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
            [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p),
            (∀ (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
                center mu delta used cert, IsAdmissibleOperator data G →
              0 < mu → 0 < delta →
              ((S.atData data hp).solve center mu delta).execute data G oracle =
                  .finished used (some cert) →
                cert.IsVerifiedFor data G delta) ∧
            (∀ (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
                center mu delta, IsAdmissibleOperator data G →
              0 < mu → 0 < delta → StronglyMonotoneOn data G mu →
              ∀ zStar, IsVISolution data G zStar →
                ∃ used cert,
                  ((S.atData data hp).solve center mu delta).execute data G oracle =
                    .finished used (some cert) ∧
                  cert.IsVerifiedFor data G delta ∧
                  (used : ℝ) ≤ strongInterfaceCost data S.leadingConstant
                    gamma b ‖center.1 - zStar‖ mu delta)) ∧
      (∀ (A : ResidualSolverFamily.{u} p),
        A.HasJointBorelCappedOutcome ↔
          (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
              [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
              (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ),
            let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
              upperEvaluatedNormalCertificateMeasurableSpace data
            ∀ n, Measurable (fun z : data.X ×
                (Fin n → data.X × SymmetricExactJet E data.p) =>
              ExactJetProgram.replayOutcomeAction
                (((A.atData data hp).solve z.1 R epsilon).installedProgram data)
                z.2)) ∧
          (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
              [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
              (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ),
            let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
              upperEvaluatedNormalCertificateMeasurableSpace data
            ∀ n, Measurable (fun z : (data.X × data.X) ×
                (Fin n → data.X × SymmetricExactJet E data.p) =>
              let shifted := data.withStart z.1.1
              let call := (A.atData shifted hp).solve z.1.2 R epsilon
              ExactJetProgram.replayOutcomeAction
                (call.anchoredInstalledProgram data z.1.1) z.2))) ∧
      (∀ (S : StrongSolverFamily.{u} p),
        S.HasJointBorelCappedOutcome ↔
          (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
              [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
              (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ),
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
            let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
              upperEvaluatedNormalCertificateMeasurableSpace data
            ∀ n, Measurable (fun z : (data.X × data.X) ×
                (Fin n → data.X × SymmetricExactJet E data.p) =>
              let shifted := data.withStart z.1.1
              let call := (S.atData shifted hp).solve z.1.2 mu delta
              ExactJetProgram.replayOutcomeAction
                (call.anchoredInstalledProgram data z.1.1) z.2))) := by
  intro p
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro solver exponent b
    rfl
  · intro solver exponent b
    rfl
  · intro solver
    rfl
  · intro solver
    rfl

end Interfaces

section BaseStrong

/-- Expanded, hash-binding construction theorem for `prop:base-strong`.
The result exposes both semantic clauses and measurable replay of the actual
installed capped program, uniformly in the center and in a changed public
anchor. -/
theorem baseStrong_source_contract (p : ℕ) :
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p),
      (∀ (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
          center mu delta used cert, IsAdmissibleOperator data G →
        0 < mu → 0 < delta →
        (((baseStrongCertifiedFamily p).atData data hp).solve center mu delta).execute
            data G oracle = .finished used (some cert) →
          cert.IsVerifiedFor data G delta) ∧
      (∀ (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G)
          center mu delta, IsAdmissibleOperator data G →
        0 < mu → 0 < delta → StronglyMonotoneOn data G mu →
        ∀ zStar, IsVISolution data G zStar →
          ∃ used cert,
            (((baseStrongCertifiedFamily p).atData data hp).solve
                center mu delta).execute data G oracle =
              .finished used (some cert) ∧
            cert.IsVerifiedFor data G delta ∧
            (used : ℝ) ≤ strongInterfaceCost data
              (baseStrongCertifiedFamily p).leadingConstant
              (2 / ((p : ℝ) + 1)) 2 ‖center.1 - zStar‖ mu delta)) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ),
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun z : data.X ×
          (Fin n → data.X × SymmetricExactJet E data.p) =>
        ExactJetProgram.replayOutcomeAction
          ((((baseStrongCertifiedFamily p).atData data hp).solve z.1 mu delta)
            |>.installedProgram data) z.2)) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ),
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun z : (data.X × data.X) ×
          (Fin n → data.X × SymmetricExactJet E data.p) =>
        let shifted := data.withStart z.1.1
        let call := ((baseStrongCertifiedFamily p).atData shifted hp).solve
          z.1.2 mu delta
        ExactJetProgram.replayOutcomeAction
          (call.anchoredInstalledProgram data z.1.1) z.2)) := by
  have hBorel := baseStrongCertifiedFamily_hasJointBorelCappedOutcome p
  refine ⟨?_, ?_, ?_⟩
  · intro E _ _ _ data hp
    exact prop_base_strong p E data hp
  · intro E _ _ _ _ _ data hp mu delta
    exact hBorel.ordinary data hp mu delta
  · intro E _ _ _ _ _ data hp mu delta
    exact hBorel.anchored data hp mu delta

end BaseStrong

section Taylor

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- Expanded, hash-binding headline for `lem:taylor`. -/
theorem taylor_source_contract
    (p : ℕ) (Lp : ℝ) (X U : Set E) (G : E → E) :
    2 ≤ p → 0 ≤ Lp → IsOpen U → X ⊆ U → Convex ℝ X →
      ContDiffOn ℝ (p - 1 : ℕ) G U →
      (∀ x ∈ X, ∀ y ∈ X,
        ‖iteratedFDeriv ℝ (p - 1) G x - iteratedFDeriv ℝ (p - 1) G y‖ ≤
          Lp * ‖x - y‖) →
      ∀ x ∈ X, ∀ y ∈ X,
        ‖G y - taylorModel p G x y‖ ≤
            Lp / (Nat.factorial p : ℝ) * ‖y - x‖ ^ p ∧
        ‖fderiv ℝ G y - taylorModelDerivative p G x y‖ ≤
          Lp / (Nat.factorial (p - 1) : ℝ) * ‖y - x‖ ^ (p - 1) := by
  exact taylorRemainderClaim_proof p Lp X U G

end Taylor

section FiniteVI

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Expanded, hash-binding headline for `lem:model-existence`: uniqueness on
every genuine queried model, continuous dependence on the admissible
center--jet subspace, and a total continuous (hence norm-Borel measurable)
ambient selector which returns the certified solution/normal pair on every
genuine queried jet. -/
theorem modelExistence_source_contract (data : VIPublicData E) :
    (∀ (G : E → E) (_hG : IsAdmissibleOperator data G)
        (oracle : FeasibleExactSymmetricJetOracle data G) (center : data.X),
      ∃! y : E, SolvesModelVI data.X
        (exactJetModel data.p data.Lp center.1 (oracle.answer center)) y) ∧
    Continuous (admissibleModelSolution data) ∧
    Continuous (borelKnownModelStep data) ∧
    @Measurable (AmbientModelParameter data) (data.X × E)
      (MeasurableSpace.prod (upperFeasibleBorelMeasurableSpace data)
        (upperJetBorelMeasurableSpace data.p))
      (MeasurableSpace.prod (upperFeasibleBorelMeasurableSpace data) (borel E))
      (borelKnownModelStep data) ∧
    (∀ (G : E → E) (hG : IsAdmissibleOperator data G)
        (oracle : FeasibleExactSymmetricJetOracle data G) (center : data.X),
      IsKnownModelStep data center (oracle.answer center)
        (borelKnownModelStep data (center, oracle.answer center))) := by
  refine ⟨(modelExistenceClaim_proof data).1,
    (modelExistenceClaim_proof data).2,
    continuous_borelKnownModelStep data, ?_, ?_⟩
  · letI : MeasurableSpace E := borel E
    letI : BorelSpace E := ⟨rfl⟩
    exact measurable_borelKnownModelStep data
  · intro G hG oracle center
    exact borelKnownModelStep_genuine_spec data G hG oracle center

/-- Source-facing Halve contract with the genuine execution guarantee, the
two local first-answer Borel obligations, and direct measurable replay of the
complete finite program on every transcript length. -/
theorem halving_borel_source_contract
    (data : VIPublicData E) (G : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data G)
    (hG : IsAdmissibleOperator data G)
    (center : data.X) (mu r : ℝ) (hmu : 0 < mu) (hr : 0 < r)
    (hstrong : StronglyMonotoneOn data G mu)
    (zStar : E) (hz : IsVISolution data G zStar)
    (hcenter : ‖center.1 - zStar‖ ≤ r) :
    (∃ used out,
      ExactJetProgram.Evaluates oracle.answer (halvingProgram data center mu r)
        used (some out) ∧
      used ≤ 2 * halvingIterationCount data.p data.Lp r mu ∧
      out.point ∈ data.X ∧ ‖out.point - zStar‖ ≤ r / 2) ∧
    @Measurable (SymmetricExactJet E data.p) data.X
      (upperJetBorelMeasurableSpace data.p)
      (upperFeasibleBorelMeasurableSpace data)
      (fun jet ↦ (knownModelStep data center jet).1) ∧
    @MeasurableSet (SymmetricExactJet E data.p)
      (upperJetBorelMeasurableSpace data.p)
      {jet | (knownModelStep data center jet).1 = center} ∧
    (let _ : MeasurableSpace E := borel E
      let _ : BorelSpace E := ⟨rfl⟩
      let _ : MeasurableSpace (HalvingOutput data) :=
        halvingOutputMeasurableSpace data
      ∀ n, Measurable (fun history :
          Fin n → data.X × SymmetricExactJet E data.p =>
        ExactJetProgram.replayOutcomeAction
          (halvingProgram data center mu r) history)) := by
  refine ⟨prop_halving data G oracle hG center mu r hmu hr hstrong zStar hz
      hcenter,
    halving_model_query_normBorel data center,
    halving_early_branch_normBorel data center, ?_⟩
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace (HalvingOutput data) :=
    halvingOutputMeasurableSpace data
  change ExactJetProgram.IsBorelOutcome (halvingProgram data center mu r)
  exact halvingProgram_isBorelOutcome data mu center r

/-- Combined source-facing headline for `lem:correction`.  Its first conjunct
is the two displayed analytic bounds.  Its second conjunct runs the genuine
model correction and binds the two original queries and evaluated normal
certificate in the same theorem signature.  The final conjunct expands the
whole two-query program's outcome measurability on every replay length. -/
theorem correction_source_contract :
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E]
        (X : Set E) (G : E → E) (p : ℕ) (hp : 2 ≤ p)
        (Lp r : ℝ) (hLp : 0 < Lp) (x y zStar n err : E),
      y ∈ X → zStar ∈ X →
      (∀ w ∈ X, 0 ≤ inner ℝ (G zStar) (w - zStar)) →
      (∀ a ∈ X, ∀ b ∈ X,
        0 ≤ inner ℝ (G a - G b) (a - b)) →
      ‖x - zStar‖ ≤ r → n ∈ normalCone X y →
      G y + n = err -
        ((2 * (p : ℝ) / p.factorial) * Lp * ‖y - x‖ ^ (p - 1)) •
          (y - x) →
      ‖err‖ ≤ Lp / p.factorial * ‖y - x‖ ^ p →
      ‖y - x‖ ≤ 3 * r ∧
        ‖G y + n‖ ≤ correctionConstant p * Lp * r ^ p) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E]
        (data : VIPublicData E) (G : E → E)
        (oracle : FeasibleExactSymmetricJetOracle data G)
        (hG : IsAdmissibleOperator data G) (x : data.X) (r : ℝ)
        (zStar : E), IsVISolution data G zStar →
      ‖x.1 - zStar‖ ≤ r →
      ∃ cert, ExactJetProgram.Evaluates oracle.answer
          (correctionProgram data x
            (correctionConstant data.p * data.Lp * r ^ data.p))
          2 (some cert) ∧
        cert.IsVerifiedFor data G
          (correctionConstant data.p * data.Lp * r ^ data.p)) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (data : VIPublicData E) (x : data.X),
      @Measurable (SymmetricExactJet E data.p) data.X
        (upperJetBorelMeasurableSpace data.p)
        (upperFeasibleBorelMeasurableSpace data)
        (fun jet ↦ (knownModelStep data x jet).1)) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (delta : ℝ),
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun z : data.X ×
          (Fin n → data.X × SymmetricExactJet E data.p) =>
        ExactJetProgram.replayOutcomeAction
          (correctionProgram data z.1 delta) z.2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E _ _ _ X G p hp Lp r hLp x y zStar n err hy hz hzvi hmono
      hradius hn hmodel htaylor
    exact lem_correction X G p hp Lp r hLp x y zStar n err hy hz hzvi hmono
      hradius hn hmodel htaylor
  · intro E _ _ _ data G oracle hG x r zStar hz hradius
    apply correctionProgram_succeeds_of_radius data G oracle hG x r
      (correctionConstant data.p * data.Lp * r ^ data.p) zStar hz hradius
      le_rfl
    exact knownModelStep_genuine_spec data G hG oracle x
  · intro E _ _ _ data x
    exact halving_model_query_normBorel data x
  · intro E _ _ _ _ _ data delta
    exact correctionProgram_isJointlyBorelOutcome data delta

private theorem audit_admissible_continuousOn
    (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) : ContinuousOn F data.X := by
  intro x hx
  obtain ⟨U, hU, hXU, hreg⟩ := hF.regularity
  exact (hreg.contDiffAt (hU.mem_nhds (hXU hx))).continuousAt.continuousWithinAt

private theorem audit_admissible_locallyLipschitzOn
    (data : VIPublicData E) (F : E → E)
    (hF : IsAdmissibleOperator data F) : LocallyLipschitzOn data.X F := by
  apply ContDiffOn.locallyLipschitzOn data.X_convex
  intro x hx
  obtain ⟨U, hU, hXU, hreg⟩ := hF.regularity
  have hp := data.p_ge_two
  have hnat : ContDiffAt ℝ (data.p - 1 : ℕ) F x :=
    hreg.contDiffAt (hU.mem_nhds (hXU hx))
  exact hnat.of_le (by
    exact_mod_cast (show 1 ≤ data.p - 1 by omega)) |>.contDiffWithinAt

section ApproximateProgramBorel

variable [MeasurableSpace E] [BorelSpace E]

/-- Whole-outcome Borel replay for the concrete two-query proximal correction.
The source contract below expands this definition rather than naming the
helper. -/
private theorem proximalModelCorrectionProgram_isBorelOutcome_contract
    (data : VIPublicData E) (eta : ℝ) (center : data.X) :
    let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
      upperEvaluatedNormalCertificateMeasurableSpace data
    ExactJetProgram.IsBorelOutcome
      (proximalModelCorrectionProgram data eta center) := by
  letI : MeasurableSpace (EvaluatedNormalCertificate data) :=
    upperEvaluatedNormalCertificateMeasurableSpace data
  let Jet := SymmetricExactJet E data.p
  let model : Jet → data.X × E := fun base =>
    knownModelStep data center
      (proxJetAnswer data.p eta center.1 center.1 base)
  have hproxNorm : @Measurable Jet Jet
      (upperJetBorelMeasurableSpace data.p)
      (upperJetBorelMeasurableSpace data.p)
      (proxJetAnswer data.p eta center.1 center.1) := by
    letI : MeasurableSpace Jet := upperJetBorelMeasurableSpace data.p
    letI : BorelSpace Jet := ⟨rfl⟩
    exact (continuous_proxJetAnswer data.p eta center.1 center.1).measurable
  have hprox : Measurable
      (proxJetAnswer data.p eta center.1 center.1) := by
    change @Measurable Jet Jet inferInstance inferInstance
      (proxJetAnswer data.p eta center.1 center.1)
    rw [upperSymmetricExactJet_measurable_eq_normBorel data.p]
    exact hproxNorm
  have hmodel : Measurable model :=
    (measurable_knownModelStep_componentwise data).comp
      (measurable_const.prodMk hprox)
  let Input := Jet × Jet
  let cert : Input → EvaluatedNormalCertificate data := fun input => ({
    point := (model input.1).1
    normal := (model input.1).2
    value := symmetricJetValue data input.2 })
  have hpoint : Measurable (fun input : Input => (model input.1).1) :=
    (measurable_fst.comp hmodel).comp measurable_fst
  have hnormal : Measurable (fun input : Input => (model input.1).2) :=
    (measurable_snd.comp hmodel).comp measurable_fst
  have hvalue : Measurable (fun input : Input =>
      symmetricJetValue data input.2) :=
    (measurable_symmetricJetValue_componentwise data).comp measurable_snd
  have hcert : Measurable cert := by
    apply measurable_evaluatedNormalCertificate_mk data
    · rw [← upperFeasible_measurable_eq_normBorel data]
      exact hpoint
    · rw [← BorelSpace.measurable_eq]
      exact hnormal
    · rw [← BorelSpace.measurable_eq]
      exact hvalue
  let terminal : Input → ExactJetProgram data.X Jet
      (EvaluatedNormalCertificate data) := fun input => .halt (some (cert input))
  have hterminal : ExactJetProgram.IsJointlyBorelOutcome terminal := by
    exact ExactJetProgram.isJointlyBorelOutcome_halt _
      (measurable_some.comp hcert)
  let afterFirst : Jet → ExactJetProgram data.X Jet
      (EvaluatedNormalCertificate data) := fun base =>
    .query (model base).1 (fun baseY => terminal (base, baseY))
  have hafterFirst : ExactJetProgram.IsJointlyBorelOutcome afterFirst := by
    exact ExactJetProgram.isJointlyBorelOutcome_query
      (fun base : Jet => (model base).1)
      (fun input : Jet × Jet => terminal input)
      (measurable_fst.comp hmodel) hterminal
  have htail : ExactJetProgram.IsJointlyBorelOutcome
      (fun input : PUnit.{1} × Jet => afterFirst input.2) :=
    hafterFirst.compParameter _ measurable_snd
  have hwhole : ExactJetProgram.IsJointlyBorelOutcome
      (fun _ : PUnit.{1} => ExactJetProgram.query center
        (fun base => afterFirst base)) :=
    ExactJetProgram.isJointlyBorelOutcome_query
      (fun _ : PUnit.{1} => center)
      (fun input : PUnit.{1} × Jet => afterFirst input.2)
      measurable_const htail
  simpa only [proximalModelCorrectionProgram, afterFirst, terminal, cert, model,
    Jet, Input] using hwhole.fixed PUnit.unit

end ApproximateProgramBorel

/-- Expanded, combined and hash-binding headline for
`prop:approx-recovery`, including direct whole-outcome Borel replay for its
actual two-query proximal correction program. -/
theorem approxRecovery_source_contract :
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (data : VIPublicData E) (F : E → E)
        (hcont : ContinuousOn F data.X)
        (hloc : LocallyLipschitzOn data.X F)
        (hmono : ∀ x ∈ data.X, ∀ y ∈ data.X,
          0 ≤ inner ℝ (F x - F y) (x - y))
        (z yHat : E), z ∈ data.X → yHat ∈ data.X →
        ∀ n, n ∈ normalCone data.X yHat →
        ∀ eta delta, ∀ heta : 0 < eta, 0 ≤ delta →
        ‖F yHat + n + eta⁻¹ • (yHat - z)‖ ≤ delta →
        let yStar := resolventPoint data.X data.X_nonempty data.X_compact
          data.X_convex F hcont hloc hmono eta heta z
        ‖yHat - yStar‖ ≤ eta * delta ∧
          tangentResidual data F yHat ≤ ‖z - yStar‖ / eta + 2 * delta) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (data : VIPublicData E) (F : E → E)
        (oracle : FeasibleExactSymmetricJetOracle data F)
        (hF : IsAdmissibleOperator data F) (center : data.X)
        (eta : ℝ) (heta : 0 < eta),
      let yStar := resolventPoint data.X data.X_nonempty data.X_compact
        data.X_convex F (audit_admissible_continuousOn data F hF)
          (audit_admissible_locallyLipschitzOn data F hF) hF.monotone_on
            eta heta center.1
      let Rz := ‖center.1 - yStar‖
      let delta := correctionConstant data.p * data.Lp * Rz ^ data.p
      ∃ cert, ExactJetProgram.Evaluates oracle.answer
          (proximalModelCorrectionProgram data eta center) 2 (some cert) ∧
        cert.IsVerifiedFor data F (Rz / eta + 2 * delta)) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (data : VIPublicData E)
        (eta : ℝ) (center : data.X),
      @Measurable (SymmetricExactJet E data.p) data.X
        (upperJetBorelMeasurableSpace data.p)
        (upperFeasibleBorelMeasurableSpace data)
        (fun base ↦ (knownModelStep data center
          (proxJetAnswer data.p eta center.1 center.1 base)).1)) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (eta : ℝ) (center : data.X),
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun history :
          Fin n → data.X × SymmetricExactJet E data.p =>
        ExactJetProgram.replayOutcomeAction
          (proximalModelCorrectionProgram data eta center) history)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E _ _ _ data F hcont hloc hmono z yHat hz hy n hn eta delta
      heta hdelta hcert
    exact approximateProximal_core data F hcont hloc hmono z yHat hz hy n hn
      eta delta heta hdelta hcert
  · intro E _ _ _ data F oracle hF center eta heta
    simpa only using proximalModelCorrection_twoQueries data F oracle hF center
      eta heta
  · intro E _ _ _ data eta center
    exact proximal_model_query_normBorel data eta center
  · intro E _ _ _ _ _ data eta center
    exact proximalModelCorrectionProgram_isBorelOutcome_contract data eta center

/-- Expanded, hash-binding headline for `lem:zero-query`.  It states the
impossibility conclusion directly; the endpoint construction remains a
stronger proof component rather than an opaque conclusion wrapper. -/
theorem zeroQuery_source_contract :
    ∀ (p : ℕ) (hp : 2 ≤ p)
      (Lp D epsilon : ℝ) (hLp : 0 < Lp) (hD : 0 < D)
      (hepsilon : 0 < epsilon)
      (policy : BorelStoppingPolicy.{0, 0, 0}
        (Answer := ZeroQueryAnswer p)
        (intervalVIData p hp Lp D hLp hD).X 0),
      ¬ ZeroQueryUniformSuccess p hp Lp D epsilon hLp hD policy := by
  intro p hp Lp D epsilon hLp hD hepsilon policy
  obtain ⟨M, _hM, _hplus, _hminus, _hmeas, _hrun, _hiffPlus,
    _hiffMinus, _hmeasPlus, _hmeasMinus, _hnotBoth, hnotUniform⟩ :=
    zeroQueryLowerClaim_proof p hp Lp D epsilon hLp hD hepsilon policy
  exact hnotUniform

section HalpernAndBoost

/-- Expanded, hash-binding headline for `lem:warm-energy`. -/
theorem warmEnergy_source_contract
    (P : E → E) (zStar x0 : E) (R e : ℝ) (K : ℕ)
    (x yHat w xBar yBar : ℕ → E) :
    FirmlyNonexpansive P → P zStar = zStar → ‖x0 - zStar‖ ≤ R →
    1 ≤ K → IsInexactHalpernOrbit P x0 e K x yHat →
    IsHalpernOrbit P x0 xBar yBar →
    IsProjectedLinearPredictor P x0 x yHat w K →
    e = R / (K + 2 : ℝ) ^ 4 →
    (‖w 0 - P (x 0)‖ ≤ 3 * R ∧ ‖w 1 - P (x 1)‖ ≤ 3 * R) ∧
    (∀ t, 2 ≤ t → t ≤ K →
      ‖w t - P (x t)‖ ≤
        ‖yBar t - (2 : ℝ) • yBar (t - 1) + yBar (t - 2)‖ +
          (2 * (t : ℝ) + 1) * e) ∧
    (∀ k ell, 2 ≤ k → k ≤ ell → ell ≤ 2 * k - 1 → ell ≤ K →
      (∑ t ∈ Finset.Icc k ell, ‖w t - P (x t)‖ ^ 2) ≤
        256 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) / (k : ℝ) ^ 2) := by
  exact warmEnergyClaim_proof P zStar x0 R e K x yHat w xBar yBar

/-- Expanded, hash-binding headline for `lem:final-cert`. -/
theorem finalCertificate_source_contract
    (X : Set E) (F P : E → E) (zStar x0 n v : E)
    (R epsilon e eta : ℝ) (K : ℕ)
    (x yHat xBar yBar : ℕ → E) :
    FirmlyNonexpansive P → P zStar = zStar → ‖x0 - zStar‖ ≤ R →
    0 < R → 0 < epsilon → 2 ≤ K →
    IsInexactHalpernOrbit P x0 e K x yHat →
    IsHalpernOrbit P x0 xBar yBar →
    n ∈ normalCone X (yHat K) →
    F (yHat K) + n = v - (1 / eta) • (yHat K - x K) →
    ‖v‖ ≤ e / eta →
    e = R / (K + 2 : ℝ) ^ 4 →
    eta = 8 * R * (1 + harmonicR (K + 1)) /
      (epsilon * (K + 1 : ℝ)) →
    n ∈ normalCone X (yHat K) ∧ ‖F (yHat K) + n‖ ≤ epsilon := by
  exact finalCertificateClaim_proof X F P zStar x0 n v R epsilon e eta K
    x yHat xBar yBar

/-- Direct construction theorem for `thm:boost`; the signature names the
actual executable family and expands both the required strong-family Borel
observable and the resulting boosted-family observable to measurable replay
of installed capped programs. -/
theorem boost_source_contract
    (p : ℕ) (S : StrongSolverFamily.{u} p) (gamma : ℝ) (b : ℕ) :
    S.SatisfiesInterface gamma b →
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ),
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun z : data.X ×
          (Fin n → data.X × SymmetricExactJet E data.p) =>
        ExactJetProgram.replayOutcomeAction
          (((S.atData data hp).solve z.1 mu delta).installedProgram data)
          z.2)) →
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ),
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun z : (data.X × data.X) ×
          (Fin n → data.X × SymmetricExactJet E data.p) =>
        let shifted := data.withStart z.1.1
        let call := (S.atData shifted hp).solve z.1.2 mu delta
        ExactJetProgram.replayOutcomeAction
          (call.anchoredInstalledProgram data z.1.1) z.2)) →
    0 < gamma → gamma ≤ 1 →
    2 / 3 ≤ ((p - 1 : ℕ) : ℝ) * gamma →
    ((p - 1 : ℕ) : ℝ) * gamma ≤ 2 →
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (data : VIPublicData E) (hp : data.p = p),
      let A := boostedResidualFamily p S gamma b
      (∀ center R epsilon,
        0 < R → R ≤ data.D → 0 < epsilon →
          ((((A.atData data hp).solve center R epsilon).cap : ℕ) : ℝ) ≤
            residualInterfaceCost data A.leadingConstant
              (boostAlpha gamma) (b + 4) R epsilon) ∧
      (∀ (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
          center R epsilon used cert, IsAdmissibleOperator data F →
        0 < R → 0 < epsilon →
        ((A.atData data hp).solve center R epsilon).execute data F oracle =
            .finished used (some cert) →
          cert.IsVerifiedFor data F epsilon) ∧
      (∀ (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
          center R epsilon, IsAdmissibleOperator data F →
        0 < R → R ≤ data.D → 0 < epsilon →
        ∀ zStar, IsVISolution data F zStar → ‖center.1 - zStar‖ ≤ R →
          ∃ used cert,
            ((A.atData data hp).solve center R epsilon).execute data F oracle =
              .finished used (some cert) ∧
            cert.IsVerifiedFor data F epsilon ∧
            (used : ℝ) ≤ residualInterfaceCost data A.leadingConstant
              (boostAlpha gamma) (b + 4) R epsilon)) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ),
      let A := boostedResidualFamily p S gamma b
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun z : data.X ×
          (Fin n → data.X × SymmetricExactJet E data.p) =>
        ExactJetProgram.replayOutcomeAction
          (((A.atData data hp).solve z.1 R epsilon).installedProgram data)
          z.2)) ∧
    (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
        (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ),
      let A := boostedResidualFamily p S gamma b
      let _ : MeasurableSpace (EvaluatedNormalCertificate data) :=
        upperEvaluatedNormalCertificateMeasurableSpace data
      ∀ n, Measurable (fun z : (data.X × data.X) ×
          (Fin n → data.X × SymmetricExactJet E data.p) =>
        let shifted := data.withStart z.1.1
        let call := (A.atData shifted hp).solve z.1.2 R epsilon
        ExactJetProgram.replayOutcomeAction
          (call.anchoredInstalledProgram data z.1.1) z.2)) := by
  intro hS hSordinary hSanchored hgamma hgamma1 ha23 ha2
  have hSBorel : S.HasJointBorelCappedOutcome := by
    constructor
    · intro E _ _ _ _ _ data hp mu delta
      exact hSordinary E data hp mu delta
    · intro E _ _ _ _ _ data hp mu delta
      exact hSanchored E data hp mu delta
  have hABorel := boostedResidualFamily_hasJointBorelCappedOutcome
    p S hSBorel gamma b
  refine ⟨?_, ?_, ?_⟩
  · intro E _ _ _ data hp
    exact boostedResidualFamily_satisfies p S gamma b hS hgamma hgamma1 ha23 ha2
      E data hp
  · intro E _ _ _ _ _ data hp R epsilon
    exact hABorel.ordinary data hp R epsilon
  · intro E _ _ _ _ _ data hp R epsilon
    exact hABorel.anchored data hp R epsilon

end HalpernAndBoost

end FiniteVI

section DistanceSensitive

/-- Direct combined corollary once the final hierarchy has supplied its
residual solver.  The source's unconditional corollary additionally needs
the still-pending restart edge, so this conditional theorem is intentionally
not yet a claim-mapping target. -/
theorem distanceSensitiveUpper_of_finalSolver_source_contract
    (p : ℕ)
    (hsolver : HasResidualSolver p
      (2 / (3 * p - 1 : ℝ)) (6 * (p - 1))) :
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
              .finished used (some cert) ∧
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
            .finished used (some cert) →
          cert.IsVerifiedFor data F epsilon) := by
  exact distanceSensitiveUpperClaim_of_solver p hsolver

end DistanceSensitive

end

end LeanArticleAudit.Pilot
