import VIReference.Pilot.DeterministicComplexity
import VIReference.Pilot.BorelRandomInstantiation
import VIReference.Pilot.Stiefel

/-!
# Consequences of the randomized finite-budget lower bound

This file isolates the measure-theoretic last step used by the article's
expected-residual conclusion.  It is independent of the construction of the
uniform Stiefel prior: once the hard event has the required probability, its
pointwise residual lower bound automatically yields a lower bound on the
extended nonnegative expectation.
-/

open MeasureTheory Set

namespace VIReference.Pilot

section TailExpectation

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A nonnegative random quantity which is at least `a` on a measurable event
has extended expectation at least `a` times the measure of that event. -/
theorem ofReal_mul_measure_le_lintegral_of_event_lower
    {mu : Measure Omega} {A : Set Omega} (hA : MeasurableSet A)
    {X : Omega -> Real} {a : Real}
    (hX : forall omega, omega ∈ A -> a <= X omega) :
    ENNReal.ofReal a * mu A <=
      ∫⁻ omega, ENNReal.ofReal (X omega) ∂mu := by
  calc
    ENNReal.ofReal a * mu A =
        ∫⁻ _omega in A, ENNReal.ofReal a ∂mu :=
      (setLIntegral_const A (ENNReal.ofReal a)).symm
    _ <= ∫⁻ omega in A, ENNReal.ofReal (X omega) ∂mu := by
      exact setLIntegral_mono' hA fun omega homega =>
        ENNReal.ofReal_le_ofReal (hX omega homega)
    _ <= ∫⁻ omega, ENNReal.ofReal (X omega) ∂mu :=
      setLIntegral_le_lintegral A _

/-- Probability lower bounds can be inserted directly into the preceding
tail-to-expectation inequality. -/
theorem ofReal_mul_probability_le_lintegral_of_event_lower
    {mu : Measure Omega} {A : Set Omega} (hA : MeasurableSet A)
    {X : Omega -> Real} {a : Real}
    (hX : forall omega, omega ∈ A -> a <= X omega)
    {q : ENNReal} (hq : q <= mu A) :
    ENNReal.ofReal a * q <=
      ∫⁻ omega, ENNReal.ofReal (X omega) ∂mu := by
  exact (mul_le_mul_left' hq (ENNReal.ofReal a)).trans
    (ofReal_mul_measure_le_lintegral_of_event_lower hA hX)

end TailExpectation

section RandomFixedFrameExpectation

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  {p N d : Nat} {profile : GateProfile} {Lp R : Real}
  {hp : 2 <= p} {hLp : 0 < Lp} {hR : 0 < R}

/-- The high-probability randomized lower bound implies the article's
expected-residual lower bound for one fixed frame.  We use `lintegral`, so no
unneeded global integrability premise is hidden in the statement. -/
theorem randomLower_expectedResidual_fixedFrame
    (prior : SequentialFramePrior E N d R)
    (run : SeededRandomRun prior p hp profile Lp hLp hR)
    {delta : Real} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hdim : RandomDimensionCondition N d delta) :
    exists omega,
      ENNReal.ofReal (randomResidualThreshold p profile Lp R N) *
          ENNReal.ofReal (1 - delta) <=
        ∫⁻ seed,
          ENNReal.ofReal
            (tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
              (hiddenOperator p profile Lp R N (prior.frame omega))
              (run.actualOutput omega seed)) ∂run.seedMeasure := by
  obtain ⟨_hjoint, omega, homega⟩ :=
    randomLower_probability_core prior run hdelta0 hdelta1 hdim
  refine ⟨omega, ?_⟩
  let A : Set run.Seed := {seed | (omega, seed) ∈ randomJointSlabEvent prior run}
  have hA : MeasurableSet A :=
    measurable_prodMk_left (randomJointSlabEvent_measurable prior run)
  apply ofReal_mul_probability_le_lintegral_of_event_lower hA
    (q := ENNReal.ofReal (1 - delta))
  · intro seed hseed
    change (omega, seed) ∈ randomJointSlabEvent prior run at hseed
    change (omega, seed) ∈ randomHardEvent prior run
    exact randomJointSlabEvent_subset_hard prior run hseed
  · exact homega

/-- The article's concrete choice `delta = 1/4`: one fixed frame is hard for
at least three quarters of the algorithm seeds. -/
theorem randomLower_threeQuarters_fixedFrame
    (prior : SequentialFramePrior E N d R)
    (run : SeededRandomRun prior p hp profile Lp hLp hR)
    (hdim : RandomDimensionCondition N d (1 / 4 : Real)) :
    exists omega,
      ENNReal.ofReal (3 / 4 : Real) <=
        run.seedMeasure {seed | (omega, seed) ∈ randomHardEvent prior run} := by
  have hcore := randomLower_probability_core prior run
    (delta := (1 / 4 : Real)) (by norm_num) (by norm_num) hdim
  obtain ⟨_hjoint, omega, homega⟩ := hcore
  refine ⟨omega, ?_⟩
  have htransfer : run.seedMeasure
      {seed | (omega, seed) ∈ randomJointSlabEvent prior run} ≤
      run.seedMeasure {seed | (omega, seed) ∈ randomHardEvent prior run} := by
    apply measure_mono
    intro seed hseed
    exact randomJointSlabEvent_subset_hard prior run hseed
  have hnum : ENNReal.ofReal (3 / 4 : Real) =
      ENNReal.ofReal (1 - (1 / 4 : Real)) := by norm_num
  rw [hnum]
  exact homega.trans htransfer

/-- A hard-threshold probability bound transfers to every smaller target
accuracy `epsilon`. -/
theorem randomLower_epsilonFailure_fixedFrame
    (prior : SequentialFramePrior E N d R)
    (run : SeededRandomRun prior p hp profile Lp hLp hR)
    {epsilon delta : Real}
    (hthreshold : epsilon < randomResidualThreshold p profile Lp R N)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hdim : RandomDimensionCondition N d delta) :
    exists omega,
      ENNReal.ofReal (1 - delta) <=
        run.seedMeasure {seed |
          epsilon <
            tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
              (hiddenOperator p profile Lp R N (prior.frame omega))
              (run.actualOutput omega seed)} := by
  obtain ⟨_hjoint, omega, homega⟩ :=
    randomLower_probability_core prior run hdelta0 hdelta1 hdim
  refine ⟨omega, homega.trans ?_⟩
  apply measure_mono
  intro seed hseed
  have hhard : (omega, seed) ∈ randomHardEvent prior run :=
    randomJointSlabEvent_subset_hard prior run hseed
  exact hthreshold.trans_le hhard

/-- Concrete `delta=1/4` failure statement at a target accuracy. -/
theorem randomLower_epsilonFailure_threeQuarters_fixedFrame
    (prior : SequentialFramePrior E N d R)
    (run : SeededRandomRun prior p hp profile Lp hLp hR)
    {epsilon : Real}
    (hthreshold : epsilon < randomResidualThreshold p profile Lp R N)
    (hdim : RandomDimensionCondition N d (1 / 4 : Real)) :
    exists omega,
      ENNReal.ofReal (3 / 4 : Real) <=
        run.seedMeasure {seed |
          epsilon <
            tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
              (hiddenOperator p profile Lp R N (prior.frame omega))
              (run.actualOutput omega seed)} := by
  have h := randomLower_epsilonFailure_fixedFrame prior run hthreshold
    (delta := (1 / 4 : Real)) (by norm_num) (by norm_num) hdim
  obtain ⟨omega, homega⟩ := h
  refine ⟨omega, ?_⟩
  convert homega using 1 <;> norm_num

/-- The article's `delta=1/4` expected-residual consequence. -/
theorem randomLower_expectedResidual_threeQuarters_fixedFrame
    (prior : SequentialFramePrior E N d R)
    (run : SeededRandomRun prior p hp profile Lp hLp hR)
    (hdim : RandomDimensionCondition N d (1 / 4 : Real)) :
    exists omega,
      ENNReal.ofReal (randomResidualThreshold p profile Lp R N) *
          ENNReal.ofReal (3 / 4 : Real) <=
        ∫⁻ seed,
          ENNReal.ofReal
            (tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
              (hiddenOperator p profile Lp R N (prior.frame omega))
              (run.actualOutput omega seed)) ∂run.seedMeasure := by
  have h := randomLower_expectedResidual_fixedFrame prior run
    (delta := (1 / 4 : Real)) (by norm_num) (by norm_num) hdim
  obtain ⟨omega, homega⟩ := h
  refine ⟨omega, ?_⟩
  convert homega using 1 <;> norm_num

/-- Operational randomized complexity consequence for any already-certified
sequential prior and exact-oracle seeded execution.  The theorem does not
construct either certificate; those remain explicit inputs. -/
theorem randomLower_randomizedOmega_fixedFrame
    (prior : SequentialFramePrior E N d R)
    (run : SeededRandomRun prior p hp profile Lp hLp hR)
    {D epsilon : Real} (hD : D = 2 * R) (hepsilon : 0 < epsilon)
    (hbudget : (N : Real) < deterministicOmegaConstant p profile *
      deterministicConditionNumber p Lp D epsilon ^
        deterministicRateExponent p)
    (hdim : RandomDimensionCondition N d (1 / 4 : Real)) :
    exists omega,
      IsAdmissibleOperator (ballVIData (E := E) p hp Lp hLp R hR)
          (hiddenOperator p profile Lp R N (prior.frame omega)) /\
        ENNReal.ofReal (3 / 4 : Real) <=
          run.seedMeasure {seed |
            epsilon <
              tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
                (hiddenOperator p profile Lp R N (prior.frame omega))
                (run.actualOutput omega seed)} /\
        ENNReal.ofReal (randomResidualThreshold p profile Lp R N) *
            ENNReal.ofReal (3 / 4 : Real) <=
          ∫⁻ seed,
            ENNReal.ofReal
              (tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
                (hiddenOperator p profile Lp R N (prior.frame omega))
                (run.actualOutput omega seed)) ∂run.seedMeasure := by
  subst D
  have hsq := squared_gate_of_budget_lt_omega_scale p hp profile
    Lp R epsilon hLp hR hepsilon N run.budget_pos hbudget
  have hclosed := finite_threshold_of_squared_complexity_gate p hp profile
    Lp R epsilon hLp hR hepsilon N hsq
  have hthreshold : epsilon < randomResidualThreshold p profile Lp R N := by
    rw [randomResidualThreshold_eq_closedForm p (by omega) profile Lp hR N]
    exact hclosed
  obtain ⟨_hjoint, omega, hslab⟩ := randomLower_probability_core prior run
    (delta := (1 / 4 : Real)) (by norm_num) (by norm_num) hdim
  have hslab34 : ENNReal.ofReal (3 / 4 : Real) ≤
      run.seedMeasure {seed |
        (omega, seed) ∈ randomJointSlabEvent prior run} := by
    have hnum : ENNReal.ofReal (3 / 4 : Real) =
        ENNReal.ofReal (1 - (1 / 4 : Real)) := by norm_num
    rw [hnum]
    exact hslab
  have hprob : ENNReal.ofReal (3 / 4 : Real) <=
      run.seedMeasure {seed |
        epsilon < tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
          (hiddenOperator p profile Lp R N (prior.frame omega))
          (run.actualOutput omega seed)} := by
    apply hslab34.trans
    apply measure_mono
    intro seed hseed
    have hhard : (omega, seed) ∈ randomHardEvent prior run :=
      randomJointSlabEvent_subset_hard prior run hseed
    exact hthreshold.trans_le hhard
  let A : Set run.Seed := {seed | (omega, seed) ∈ randomJointSlabEvent prior run}
  have hA : MeasurableSet A :=
    measurable_prodMk_left (randomJointSlabEvent_measurable prior run)
  have hexpect : ENNReal.ofReal (randomResidualThreshold p profile Lp R N) *
        ENNReal.ofReal (3 / 4 : Real) <=
      ∫⁻ seed,
        ENNReal.ofReal
          (tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
            (hiddenOperator p profile Lp R N (prior.frame omega))
            (run.actualOutput omega seed)) ∂run.seedMeasure := by
    apply ofReal_mul_probability_le_lintegral_of_event_lower hA
      (q := ENNReal.ofReal (3 / 4 : Real))
    · intro seed hseed
      change (omega, seed) ∈ randomJointSlabEvent prior run at hseed
      change (omega, seed) ∈ randomHardEvent prior run
      exact randomJointSlabEvent_subset_hard prior run hseed
    · exact hslab34
  refine ⟨omega, ?_, hprob, hexpect⟩
  exact hiddenOperator_admissible p hp profile hLp hR run.budget_pos
    (prior.frame omega) (prior.orthonormal omega)

end RandomFixedFrameExpectation

section CertifiedHaarExecution

open scoped RealInnerProductSpace

/-- The two still-conditional inputs for the article's concrete randomized
oracle model, packaged without an axiom:

* `adapted_projection_mgf` is the missing Stiefel conditional-sphere theorem;
* `execution` is the Borel stopped exact-oracle simulation/coupling witness.

Everything downstream of these fields is proved in this file. -/
structure CertifiedHaarBorelExecution
    (p : Nat) (hp : 2 <= p) (profile : GateProfile)
    (Lp : Real) (hLp : 0 < Lp) (R : Real) (hR : 0 < R)
    (N d : Nat) [NeZero d] where
  frame_dimension : hiddenM N < d
  adapted_projection_mgf :
    HaarStiefelAdaptedProjectionMGF (R := R) frame_dimension.le hR frame_dimension
  policy : BorelStoppingPolicy
    (Answer := SymmetricExactJet (EuclideanSpace Real (Fin d)) p)
    (Metric.closedBall (0 : EuclideanSpace Real (Fin d)) R) N
  execution : BorelRandomExecution
    (haarSequentialFramePriorOfProjectionMGF frame_dimension.le hR frame_dimension
      adapted_projection_mgf)
    p hp profile Lp hLp hR policy

namespace CertifiedHaarBorelExecution

variable {p N d : Nat} [NeZero d] {profile : GateProfile} {Lp R : Real}
  {hp : 2 <= p} {hLp : 0 < Lp} {hR : 0 < R}

/-- Build the operational certificate from an arbitrary Borel stopping policy.
The exact-oracle execution is now canonical; the adapted Haar projection MGF
is the only remaining geometric input. -/
noncomputable def ofCanonicalPolicy
    (p : Nat) (hp : 2 <= p) (profile : GateProfile)
    (Lp : Real) (hLp : 0 < Lp) (R : Real) (hR : 0 < R)
    (N d : Nat) [NeZero d]
    (hmdlt : hiddenM N < d)
    (hmgf : HaarStiefelAdaptedProjectionMGF
      (R := R) hmdlt.le hR hmdlt)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet (EuclideanSpace Real (Fin d)) p)
      (Metric.closedBall (0 : EuclideanSpace Real (Fin d)) R) N)
    (fill : Metric.closedBall (0 : EuclideanSpace Real (Fin d)) R)
    (dummy : SymmetricExactJet (EuclideanSpace Real (Fin d)) p) :
    CertifiedHaarBorelExecution p hp profile Lp hLp R hR N d := by
  let prior := haarSequentialFramePriorOfProjectionMGF
    hmdlt.le hR hmdlt hmgf
  have hframe : Measurable prior.frame := by
    exact measurable_haarSequentialFramePrior_frame hmdlt.le
      (haarStiefelAdaptedSlabTail_of_projectionMGF hmdlt.le hR hmdlt hmgf)
  exact
    { frame_dimension := hmdlt
      adapted_projection_mgf := hmgf
      policy := policy
      execution := canonicalBorelRandomExecution prior p hp profile Lp hLp hR
        hframe policy fill dummy }

/-- The concrete normalized-Haar Stiefel prior determined by the certificate. -/
noncomputable def prior
    (cert : CertifiedHaarBorelExecution p hp profile Lp hLp R hR N d) :
    SequentialFramePrior (EuclideanSpace Real (Fin d)) N d R :=
  haarSequentialFramePriorOfProjectionMGF cert.frame_dimension.le hR
    cert.frame_dimension cert.adapted_projection_mgf

/-- The exact stopped Borel execution viewed by the probability layer. -/
noncomputable def seededRun
    (cert : CertifiedHaarBorelExecution p hp profile Lp hLp R hR N d)
    (hN : 1 <= N) :
    SeededRandomRun cert.prior p hp profile Lp hLp hR :=
  cert.execution.toSeededRandomRun hN

@[simp] theorem seededRun_seedMeasure
    (cert : CertifiedHaarBorelExecution p hp profile Lp hLp R hR N d)
    (hN : 1 <= N) :
    (cert.seededRun hN).seedMeasure = cert.policy.seedMeasure := rfl

@[simp] theorem seededRun_actualOutput_eq
    (cert : CertifiedHaarBorelExecution p hp profile Lp hLp R hR N d)
    (hN : 1 <= N) (Q : RealOrthogonalGroup d) (seed : cert.policy.Seed) :
    (cert.seededRun hN).actualOutput Q seed =
      (cert.execution.actualOutput Q seed).1 := rfl

/-- On the good slab, the genuine final-oracle output agrees with the online
truncated simulation used by the concentration proof. -/
theorem seededRun_actualOutput_eq_simulation_on_slab
    (cert : CertifiedHaarBorelExecution p hp profile Lp hLp R hR N d)
    (hN : 1 <= N) (Q : RealOrthogonalGroup d) (seed : cert.policy.Seed)
    (hslab : Q ∈ randomSlabEvent cert.prior
      ((cert.seededRun hN).simulation seed)) :
    (cert.seededRun hN).actualOutput Q seed =
      ((cert.seededRun hN).simulation seed).output Q := by
  rw [seededRun_actualOutput_eq]
  rw [cert.execution.actualOutput_eq_on_slab Q seed hslab]
  exact cert.execution.output_eq Q seed

end CertifiedHaarBorelExecution

variable {p N d : Nat} [NeZero d] {profile : GateProfile} {Lp R : Real}
  {hp : 2 <= p} {hLp : 0 < Lp} {hR : 0 < R}

/-- Conditional but otherwise operational randomized Omega conclusion for the
seeded run induced by the actual Borel policy.  The Stiefel MGF bridge and
execution-coupling bridge occur visibly in `cert`; this theorem is therefore
not advertised as an unconditional proof of `thm:random`.  The companion
`seededRun_actualOutput_eq` identifies this run's output pointwise with the
saved output of the Borel execution. -/
theorem certifiedHaarBorel_randomizedOmega_fixedFrame
    (cert : CertifiedHaarBorelExecution p hp profile Lp hLp R hR N d)
    (hN : 1 <= N) {D epsilon : Real} (hD : D = 2 * R)
    (hepsilon : 0 < epsilon)
    (hbudget : (N : Real) < deterministicOmegaConstant p profile *
      deterministicConditionNumber p Lp D epsilon ^
        deterministicRateExponent p)
    (hdim : RandomDimensionCondition N d (1 / 4 : Real)) :
    exists Q : RealOrthogonalGroup d,
      IsAdmissibleOperator
          (ballVIData (E := EuclideanSpace Real (Fin d)) p hp Lp hLp R hR)
          (hiddenOperator p profile Lp R N (cert.prior.frame Q)) /\
        ENNReal.ofReal (3 / 4 : Real) <=
          (cert.seededRun hN).seedMeasure {seed |
            epsilon < tangentResidual
              (ballVIData (E := EuclideanSpace Real (Fin d)) p hp Lp hLp R hR)
              (hiddenOperator p profile Lp R N (cert.prior.frame Q))
              ((cert.seededRun hN).actualOutput Q seed)} /\
        ENNReal.ofReal (randomResidualThreshold p profile Lp R N) *
            ENNReal.ofReal (3 / 4 : Real) <=
          ∫⁻ seed,
            ENNReal.ofReal
              (tangentResidual
                (ballVIData (E := EuclideanSpace Real (Fin d)) p hp Lp hLp R hR)
                (hiddenOperator p profile Lp R N (cert.prior.frame Q))
                ((cert.seededRun hN).actualOutput Q seed))
              ∂(cert.seededRun hN).seedMeasure := by
  exact randomLower_randomizedOmega_fixedFrame cert.prior (cert.seededRun hN)
    hD hepsilon hbudget hdim

/-- Audit-facing **conditional** operational complexity statement for the
randomized argument.  It deliberately quantifies a
`CertifiedHaarBorelExecution`: the normalized-Haar adapted-projection MGF and
the measurable exact-oracle execution/coupling are premises, not conclusions.

The conclusion displays one fixed frame that is hard for at least `3/4` of
the seeds and the corresponding extended expected-residual lower bound.  The
constant depends only on `p` and the fixed gate profile, exactly as in the
deterministic inversion.  This proposition must not be identified with the
unconditional source theorem until both certificate fields are constructed. -/
def ConditionalHaarRandomizedOmegaOperationalClaim : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile),
    ∃ c_p : ℝ, c_p = deterministicOmegaConstant p profile ∧ 0 < c_p ∧
      ∀ (Lp R D epsilon : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
        (hD : D = 2 * R) (hepsilon : 0 < epsilon)
        (N d : ℕ) [NeZero d] (hN : 1 ≤ N)
        (cert : CertifiedHaarBorelExecution p hp profile Lp hLp R hR N d),
        (N : ℝ) < c_p *
            deterministicConditionNumber p Lp D epsilon ^
              deterministicRateExponent p →
        RandomDimensionCondition N d (1 / 4 : ℝ) →
        ∃ Q : RealOrthogonalGroup d,
          IsAdmissibleOperator
              (ballVIData (E := EuclideanSpace ℝ (Fin d)) p hp Lp hLp R hR)
              (hiddenOperator p profile Lp R N (cert.prior.frame Q)) ∧
            ENNReal.ofReal (3 / 4 : ℝ) ≤
              (cert.seededRun hN).seedMeasure {seed |
                epsilon < tangentResidual
                  (ballVIData (E := EuclideanSpace ℝ (Fin d))
                    p hp Lp hLp R hR)
                  (hiddenOperator p profile Lp R N (cert.prior.frame Q))
                  ((cert.seededRun hN).actualOutput Q seed)} ∧
            ENNReal.ofReal (hiddenResidualClosedForm p profile Lp R N) *
                ENNReal.ofReal (3 / 4 : ℝ) ≤
              ∫⁻ seed,
                ENNReal.ofReal
                  (tangentResidual
                    (ballVIData (E := EuclideanSpace ℝ (Fin d))
                      p hp Lp hLp R hR)
                    (hiddenOperator p profile Lp R N (cert.prior.frame Q))
                    ((cert.seededRun hN).actualOutput Q seed))
                  ∂(cert.seededRun hN).seedMeasure

/-- Kernel proof of the conditional operational statement. -/
theorem conditionalHaarRandomizedOmegaOperationalClaim_proof :
    ConditionalHaarRandomizedOmegaOperationalClaim := by
  intro p hp profile
  refine ⟨deterministicOmegaConstant p profile, rfl,
    deterministicOmegaConstant_pos p hp profile, ?_⟩
  intro Lp R D epsilon hLp hR hD hepsilon N d _instD hN cert hbudget hdim
  obtain ⟨Q, hadm, hprob, hexpect⟩ :=
    certifiedHaarBorel_randomizedOmega_fixedFrame cert hN hD hepsilon
      hbudget hdim
  refine ⟨Q, hadm, hprob, ?_⟩
  rw [← randomResidualThreshold_eq_closedForm p (by omega) profile Lp hR N]
  exact hexpect

end CertifiedHaarExecution

end VIReference.Pilot
