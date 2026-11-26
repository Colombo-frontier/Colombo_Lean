import VIReference.Pilot.StiefelBlock
import VIReference.Pilot.BorelRandomInstantiation
import VIReference.Pilot.DeterministicComplexity
import VIReference.Pilot.RandomComplexity

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace VIReference.Pilot

noncomputable section

section CombinedProbability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {p N d : ℕ} {profile : GateProfile} {Lp R : ℝ}
  {hp : 2 ≤ p} {hLp : 0 < Lp} {hR : 0 < R}

/-- The general-delta joint bound, fixed-frame bound, and expectation bound,
with the same fixed frame in the latter two conclusions. -/
theorem randomLower_joint_fixed_expected
    (prior : SequentialFramePrior E N d R)
    (run : SeededRandomRun prior p hp profile Lp hLp hR)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hdim : RandomDimensionCondition N d delta) :
    ENNReal.ofReal (1 - delta) ≤
        (prior.measure.prod run.seedMeasure) (randomHardEvent prior run) ∧
      ∃ omega,
        IsAdmissibleOperator (ballVIData (E := E) p hp Lp hLp R hR)
            (hiddenOperator p profile Lp R N (prior.frame omega)) ∧
        ENNReal.ofReal (1 - delta) ≤
          run.seedMeasure {seed | (omega, seed) ∈ randomHardEvent prior run} ∧
        ENNReal.ofReal (randomResidualThreshold p profile Lp R N) *
            ENNReal.ofReal (1 - delta) ≤
          ∫⁻ seed, ENNReal.ofReal
            (tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
              (hiddenOperator p profile Lp R N (prior.frame omega))
              (run.actualOutput omega seed)) ∂run.seedMeasure := by
  obtain ⟨hjointSlab, omega, hfixedSlab⟩ :=
    randomLower_probability_core prior run hdelta0 hdelta1 hdim
  have hjointHard : ENNReal.ofReal (1 - delta) ≤
      (prior.measure.prod run.seedMeasure) (randomHardEvent prior run) := by
    exact hjointSlab.trans (measure_mono (randomJointSlabEvent_subset_hard prior run))
  have hfixedHard : ENNReal.ofReal (1 - delta) ≤
      run.seedMeasure {seed | (omega, seed) ∈ randomHardEvent prior run} := by
    exact hfixedSlab.trans (measure_mono fun seed hseed =>
      randomJointSlabEvent_subset_hard prior run hseed)
  let A : Set run.Seed :=
    {seed | (omega, seed) ∈ randomJointSlabEvent prior run}
  have hA : MeasurableSet A :=
    measurable_prodMk_left (randomJointSlabEvent_measurable prior run)
  have hexpect : ENNReal.ofReal (randomResidualThreshold p profile Lp R N) *
        ENNReal.ofReal (1 - delta) ≤
      ∫⁻ seed, ENNReal.ofReal
        (tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
          (hiddenOperator p profile Lp R N (prior.frame omega))
          (run.actualOutput omega seed)) ∂run.seedMeasure := by
    apply ofReal_mul_probability_le_lintegral_of_event_lower hA
      (q := ENNReal.ofReal (1 - delta))
    · intro seed hseed
      change (omega, seed) ∈ randomJointSlabEvent prior run at hseed
      change (omega, seed) ∈ randomHardEvent prior run
      exact randomJointSlabEvent_subset_hard prior run hseed
    · exact hfixedSlab
  refine ⟨hjointHard, omega, ?_, hfixedHard, hexpect⟩
  exact hiddenOperator_admissible p hp profile hLp hR run.budget_pos
    (prior.frame omega) (prior.orthonormal omega)

end CombinedProbability

section Concrete

noncomputable def canonicalHaarPrior
    {N d : ℕ} {R : ℝ} (hmdlt : hiddenM N < d) (hR : 0 < R) :
    SequentialFramePrior (EuclideanSpace ℝ (Fin d)) N d R :=
  haarSequentialFramePriorConcrete hmdlt.le hR hmdlt

theorem measurable_canonicalHaarPrior_frame
    {N d : ℕ} {R : ℝ} (hmdlt : hiddenM N < d) (hR : 0 < R) :
    Measurable (canonicalHaarPrior hmdlt hR).frame := by
  exact measurable_haarSequentialFramePrior_frame hmdlt.le
    (haarStiefelAdaptedSlabTail_proof hmdlt.le hR hmdlt)

noncomputable def canonicalHaarExecution
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R)
    (N d : ℕ) [NeZero d] (hmdlt : hiddenM N < d)
    (policy : BorelStoppingPolicy.{0, 0, 0}
      (Answer := SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) N)
    (fill : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)
    (dummy : SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p) :
    BorelRandomExecution (canonicalHaarPrior hmdlt hR)
      p hp profile Lp hLp hR policy :=
  canonicalBorelRandomExecution (canonicalHaarPrior hmdlt hR)
    p hp profile Lp hLp hR (measurable_canonicalHaarPrior_frame hmdlt hR)
    policy fill dummy

noncomputable def canonicalHaarSeededRun
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R)
    (N d : ℕ) [NeZero d] (hN : 1 ≤ N) (hmdlt : hiddenM N < d)
    (policy : BorelStoppingPolicy.{0, 0, 0}
      (Answer := SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) N)
    (fill : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)
    (dummy : SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p) :
    SeededRandomRun (canonicalHaarPrior hmdlt hR)
      p hp profile Lp hLp hR :=
  (canonicalHaarExecution p hp profile Lp hLp R hR N d hmdlt
    policy fill dummy).toSeededRandomRun hN

@[simp] theorem canonicalHaarSeededRun_actualOutput
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R)
    (N d : ℕ) [NeZero d] (hN : 1 ≤ N) (hmdlt : hiddenM N < d)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) N)
    (fill : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)
    (dummy : SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
    (Q : RealOrthogonalGroup d) (seed : policy.Seed) :
    (canonicalHaarSeededRun p hp profile Lp hLp R hR N d hN hmdlt
      policy fill dummy).actualOutput Q seed =
      (actualHiddenRunnerOutput (canonicalHaarPrior hmdlt hR)
        p hp profile Lp hLp hR policy fill dummy Q seed).1 := rfl

end Concrete

/-- Exact finite-budget content of `thm:random` for the canonical smooth gate.
The first conjunct records globally that the output in the probability event
comes from a genuine execution against the final hidden exact oracle. -/
def RandomFiniteBoundClaim : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p)
    (Lp R : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (N d : ℕ) [NeZero d] (hN : 1 ≤ N)
    (delta : ℝ) (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hdim : RandomDimensionCondition N d delta)
    (policy : BorelStoppingPolicy.{0, 0, 0}
      (Answer := SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) N)
    (fill : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)
    (dummy : SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p),
    let hmdlt : hiddenM N < d :=
      hiddenM_lt_of_randomDimensionCondition hdelta0 hdelta1 hdim
    let prior := canonicalHaarPrior hmdlt hR
    let exec := canonicalHaarExecution p hp standardGateProfile Lp hLp R hR
      N d hmdlt policy fill dummy
    (∀ Q seed, ∃ n, ∃ hn : n ≤ N,
      ∃ history : OracleHistory
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)
          (SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p) n,
        policy.IsUnpaddedRun
          (finalHiddenExactOracle p hp standardGateProfile Lp hLp R hR N
            (prior.frame Q)).answer
          seed n hn history (exec.actualOutput Q seed)) ∧
    (∀ Q : RealOrthogonalGroup d,
      IsAdmissibleOperator
        (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
        (hiddenOperator p standardGateProfile Lp R N (prior.frame Q))) ∧
    ENNReal.ofReal (1 - delta) ≤
      (prior.measure.prod policy.seedMeasure) {z |
        hiddenResidualClosedForm p standardGateProfile Lp R N ≤
          tangentResidual
            (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
            (hiddenOperator p standardGateProfile Lp R N (prior.frame z.1))
            (exec.actualOutput z.1 z.2).1} ∧
    ∃ Q : RealOrthogonalGroup d,
      IsAdmissibleOperator
          (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
          (hiddenOperator p standardGateProfile Lp R N (prior.frame Q)) ∧
      ENNReal.ofReal (1 - delta) ≤ policy.seedMeasure {seed |
        hiddenResidualClosedForm p standardGateProfile Lp R N ≤
          tangentResidual
            (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
            (hiddenOperator p standardGateProfile Lp R N (prior.frame Q))
            (exec.actualOutput Q seed).1} ∧
      ENNReal.ofReal (hiddenResidualClosedForm p standardGateProfile Lp R N) *
          ENNReal.ofReal (1 - delta) ≤
        ∫⁻ seed, ENNReal.ofReal
          (tangentResidual
            (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
            (hiddenOperator p standardGateProfile Lp R N (prior.frame Q))
            (exec.actualOutput Q seed).1) ∂policy.seedMeasure

/-- Operational `delta=1/4` consequence with `D=2R`, a positive constant
depending only on `p`, and the displayed exponent `2/(3p-1)`. -/
def RandomOmegaOperationalClaim : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p),
    ∃ c_p : ℝ,
      c_p = deterministicOmegaConstant p standardGateProfile ∧ 0 < c_p ∧
      ∀ (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
        (hD : D = 2 * R) (hepsilon : 0 < epsilon)
        (N d : ℕ) [NeZero d] (hN : 1 ≤ N)
        (policy : BorelStoppingPolicy.{0, 0, 0}
          (Answer := SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R) N)
        (fill : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)
        (dummy : SymmetricExactJet (EuclideanSpace ℝ (Fin d)) p)
        (hbudget : (N : ℝ) < c_p *
          deterministicConditionNumber p Lp D epsilon ^
            (2 / (3 * (p : ℝ) - 1)))
        (hdim : RandomDimensionCondition N d (1 / 4 : ℝ)),
        let hmdlt : hiddenM N < d :=
          hiddenM_lt_of_randomDimensionCondition (by norm_num) (by norm_num)
            hdim
        let prior := canonicalHaarPrior hmdlt hR
        let exec := canonicalHaarExecution p hp standardGateProfile Lp hLp R hR
          N d hmdlt policy fill dummy
        ∃ Q : RealOrthogonalGroup d,
          IsAdmissibleOperator
              (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
              (hiddenOperator p standardGateProfile Lp R N (prior.frame Q)) ∧
          ENNReal.ofReal (3 / 4 : ℝ) ≤ policy.seedMeasure {seed |
            epsilon < tangentResidual
              (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
              (hiddenOperator p standardGateProfile Lp R N (prior.frame Q))
              (exec.actualOutput Q seed).1} ∧
          ENNReal.ofReal
              (hiddenResidualClosedForm p standardGateProfile Lp R N) *
              ENNReal.ofReal (3 / 4 : ℝ) ≤
            ∫⁻ seed, ENNReal.ofReal
              (tangentResidual
                (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
                (hiddenOperator p standardGateProfile Lp R N (prior.frame Q))
                (exec.actualOutput Q seed).1) ∂policy.seedMeasure

/-- Full audit-facing content of `thm:random`.  The lower-family theorem is
stated for `N ≥ 1`; the separate zero-query lemma handles the global
complexity boundary exactly as in the source. -/
def RandomTheoremClaim : Prop :=
  RandomFiniteBoundClaim ∧ RandomOmegaOperationalClaim

theorem randomFiniteBoundClaim_proof : RandomFiniteBoundClaim := by
  intro p hp Lp R hLp hR N d _instD hN delta hdelta0 hdelta1 hdim
    policy fill dummy
  dsimp only
  let hmdlt : hiddenM N < d :=
    hiddenM_lt_of_randomDimensionCondition hdelta0 hdelta1 hdim
  let prior := canonicalHaarPrior hmdlt hR
  let exec := canonicalHaarExecution p hp standardGateProfile Lp hLp R hR
    N d hmdlt policy fill dummy
  let run := exec.toSeededRandomRun hN
  refine ⟨?_, ?_, ?_⟩
  · intro Q seed
    exact exec.actual_run Q seed
  · intro Q
    exact hiddenOperator_admissible p hp standardGateProfile hLp hR hN
      (prior.frame Q) (prior.orthonormal Q)
  · have hcore := randomLower_joint_fixed_expected prior run
      hdelta0 hdelta1 hdim
    simp only [randomHardEvent] at hcore
    rw [randomResidualThreshold_eq_closedForm p (by omega)
      standardGateProfile Lp hR N] at hcore
    dsimp only [run, exec, prior, canonicalHaarExecution,
      BorelRandomExecution.toSeededRandomRun] at hcore
    exact hcore

theorem randomOmegaOperationalClaim_proof : RandomOmegaOperationalClaim := by
  intro p hp
  refine ⟨deterministicOmegaConstant p standardGateProfile, rfl,
    deterministicOmegaConstant_pos p hp standardGateProfile, ?_⟩
  intro Lp R D epsilon hLp hR hD hepsilon N d _instD hN policy fill dummy
    hbudget hdim
  dsimp only
  let hmdlt : hiddenM N < d :=
    hiddenM_lt_of_randomDimensionCondition (by norm_num) (by norm_num) hdim
  let prior := canonicalHaarPrior hmdlt hR
  let exec := canonicalHaarExecution p hp standardGateProfile Lp hLp R hR
    N d hmdlt policy fill dummy
  let run := exec.toSeededRandomRun hN
  have hbudget' : (N : ℝ) <
      deterministicOmegaConstant p standardGateProfile *
        deterministicConditionNumber p Lp D epsilon ^
          deterministicRateExponent p := by
    simpa only [deterministicRateExponent] using hbudget
  have homega := randomLower_randomizedOmega_fixedFrame prior run hD hepsilon
    hbudget' hdim
  rw [randomResidualThreshold_eq_closedForm p (by omega)
    standardGateProfile Lp hR N] at homega
  dsimp only [run, exec, prior, canonicalHaarExecution,
    BorelRandomExecution.toSeededRandomRun] at homega
  exact homega

theorem randomTheoremClaim_proof : RandomTheoremClaim :=
  ⟨randomFiniteBoundClaim_proof, randomOmegaOperationalClaim_proof⟩

end

end VIReference.Pilot
