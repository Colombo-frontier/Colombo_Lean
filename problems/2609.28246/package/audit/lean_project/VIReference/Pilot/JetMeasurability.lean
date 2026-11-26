import VIReference.Pilot.JetParameterContinuity

/-!
# Measurability bridge for concrete symmetric exact-jet oracles

This file isolates the analytic obligation for instantiating the executable
Borel runner.  Symmetry certificates are proof fields and therefore introduce
no additional measurability requirement: it is enough to prove joint
measurability of the underlying iterated Fréchet derivatives.
-/

open Set MeasureTheory

namespace VIReference.Pilot

section ExactJetBridge

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- An arbitrary family of exact symmetric-jet oracles is jointly measurable
once every underlying tensor component is jointly measurable.  The possibly
noncanonical symmetry proofs stored in `oracle` disappear by proof
irrelevance. -/
theorem exactSymmetricJetOracle_answer_jointlyMeasurable
    (data : VIPublicData E) {F : Ω → E → E}
    (oracle : ∀ omega, ExactSymmetricJetOracle data (F omega))
    (hcomponents : ∀ j : Fin data.p,
      Measurable (fun z : Ω × E => iteratedFDeriv ℝ j.1 (F z.1) z.2)) :
    Measurable (fun z : Ω × E => (oracle z.1).answer z.2) := by
  refine measurable_pi_lambda _ fun j => ?_
  have hsymm : ∀ z : Ω × E,
      IsSymmetricContinuousMultilinearMap E
        (iteratedFDeriv ℝ j.1 (F z.1) z.2) := by
    intro z sigma
    rw [← (oracle z.1).exact z.2 j]
    exact ((oracle z.1).answer z.2 j).2 sigma
  have hm : Measurable (fun z : Ω × E =>
      (⟨iteratedFDeriv ℝ j.1 (F z.1) z.2, hsymm z⟩ :
        SymmetricContinuousMultilinearMap E j.1)) :=
    (hcomponents j).subtype_mk
  convert hm using 1
  funext z
  apply Subtype.ext
  exact (oracle z.1).exact z.2 j

/-- Restricted-domain version used by a feasible-set oracle runner. -/
theorem exactSymmetricJetOracle_answer_jointlyMeasurableOn
    (data : VIPublicData E) {F : Ω → E → E} (X : Set E)
    (oracle : ∀ omega, ExactSymmetricJetOracle data (F omega))
    (hcomponents : ∀ j : Fin data.p,
      Measurable (fun z : Ω × X =>
        iteratedFDeriv ℝ j.1 (F z.1) z.2.1)) :
    Measurable (fun z : Ω × X => (oracle z.1).answer z.2.1) := by
  refine measurable_pi_lambda _ fun j => ?_
  have hsymm : ∀ z : Ω × X,
      IsSymmetricContinuousMultilinearMap E
        (iteratedFDeriv ℝ j.1 (F z.1) z.2.1) := by
    intro z sigma
    rw [← (oracle z.1).exact z.2.1 j]
    exact ((oracle z.1).answer z.2.1 j).2 sigma
  have hm : Measurable (fun z : Ω × X =>
      (⟨iteratedFDeriv ℝ j.1 (F z.1) z.2.1, hsymm z⟩ :
        SymmetricContinuousMultilinearMap E j.1)) :=
    (hcomponents j).subtype_mk
  convert hm using 1
  funext z
  apply Subtype.ext
  exact (oracle z.1).exact z.2.1 j

end ExactJetBridge

section HiddenOperatorComponents

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The precise deterministic analytic obligation for truncated hidden
operators.  It is stated before composition with a random frame, so it does
not mix smooth tensor calculus with probability-space bookkeeping. -/
def TruncatedHiddenJetParameterContinuous (p : ℕ) (profile : GateProfile)
    (Lp R : ℝ) (N : ℕ) : Prop :=
  ∀ (t : Fin N) (j : Fin p),
    Continuous (fun z : (Fin (N + 1) → E) × E =>
      iteratedFDeriv ℝ j.1
        (truncatedHiddenOperator p profile Lp R N t.1 z.1) z.2)

/-- The corresponding deterministic obligation for the final hidden
operator. -/
def FinalHiddenJetParameterContinuous (p : ℕ) (profile : GateProfile)
    (Lp R : ℝ) (N : ℕ) : Prop :=
  ∀ j : Fin p,
    Continuous (fun z : (Fin (N + 1) → E) × E =>
      iteratedFDeriv ℝ j.1
        (hiddenOperator p profile Lp R N z.1) z.2)

/-- The truncated hidden construction satisfies its parameter-continuity
contract at every jet order, by the explicit rank-one tensor formula. -/
theorem truncatedHiddenJetParameterContinuous_proved
    (p : ℕ) (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N : ℕ) :
    TruncatedHiddenJetParameterContinuous (E := E) p profile Lp R N := by
  intro t j
  exact continuous_truncatedHiddenOperator_iteratedFDeriv
    j.1 p profile Lp hR N t.1

/-- The final hidden construction satisfies its parameter-continuity contract
at every jet order. -/
theorem finalHiddenJetParameterContinuous_proved
    (p : ℕ) (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N : ℕ) :
    FinalHiddenJetParameterContinuous (E := E) p profile Lp R N := by
  intro j
  exact continuous_hiddenOperator_iteratedFDeriv
    j.1 p profile Lp hR N

/-- A measurable random frame and the deterministic parameter-continuity
statement imply joint measurability of every truncated tensor component. -/
theorem truncatedHiddenJetComponents_jointlyMeasurable
    (p : ℕ) (profile : GateProfile) (Lp R : ℝ) (N : ℕ)
    (frame : Ω → Fin (N + 1) → E) (hframe : Measurable frame)
    (hcontinuous : TruncatedHiddenJetParameterContinuous
      (E := E) p profile Lp R N) (t : Fin N) (j : Fin p) :
    Measurable (fun z : Ω × E =>
      iteratedFDeriv ℝ j.1
        (truncatedHiddenOperator p profile Lp R N t.1 (frame z.1)) z.2) := by
  have harg : Measurable (fun z : Ω × E => (frame z.1, z.2)) :=
    (hframe.comp measurable_fst).prodMk measurable_snd
  convert (hcontinuous t j).measurable.comp harg using 1 <;> rfl

/-- The analogous composition lemma for the final hidden operator. -/
theorem finalHiddenJetComponents_jointlyMeasurable
    (p : ℕ) (profile : GateProfile) (Lp R : ℝ) (N : ℕ)
    (frame : Ω → Fin (N + 1) → E) (hframe : Measurable frame)
    (hcontinuous : FinalHiddenJetParameterContinuous
      (E := E) p profile Lp R N) (j : Fin p) :
    Measurable (fun z : Ω × E =>
      iteratedFDeriv ℝ j.1
        (hiddenOperator p profile Lp R N (frame z.1)) z.2) := by
  have harg : Measurable (fun z : Ω × E => (frame z.1, z.2)) :=
    (hframe.comp measurable_fst).prodMk measurable_snd
  convert (hcontinuous j).measurable.comp harg using 1 <;> rfl

end HiddenOperatorComponents

section ConcreteRunnerBridge

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Weakest componentwise proposition needed by the runner for this concrete
stage family.  Unlike the parameter-continuity interface above, it asks only
for measurability on the feasible closed ball. -/
def TruncatedHiddenStageJetMeasurable
    (p : ℕ) (profile : GateProfile) (Lp R : ℝ) (N : ℕ)
    (frame : Ω → Fin (N + 1) → E) : Prop :=
  ∀ (t : Fin N) (j : Fin p),
    Measurable (fun z : Ω × Metric.closedBall (0 : E) R =>
      iteratedFDeriv ℝ j.1
        (truncatedHiddenOperator p profile Lp R N t.1 (frame z.1)) z.2.1)

/-- The minimal componentwise proposition directly yields the runner's joint
stage-oracle measurability contract. -/
theorem truncatedHiddenStageOracle_jointlyMeasurable_of_components
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (frame : Ω → Fin (N + 1) → E)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E p) (Metric.closedBall (0 : E) R) N)
    (stageOracle : (omega : Ω) → (t : Fin N) →
      ExactSymmetricJetOracle
        (ballVIData (E := E) p hp Lp hLp R hR)
        (truncatedHiddenOperator p profile Lp R N t.1 (frame omega)))
    (hcomponents : TruncatedHiddenStageJetMeasurable
      (E := E) p profile Lp R N frame) :
    BorelStoppingPolicy.JointlyMeasurableStageOracle policy
      (fun omega t x => (stageOracle omega t).answer x) := by
  intro t
  exact exactSymmetricJetOracle_answer_jointlyMeasurableOn
    (ballVIData (E := E) p hp Lp hLp R hR)
    (Metric.closedBall (0 : E) R) (fun omega => stageOracle omega t)
    (hcomponents t)

/-- Concrete truncated exact-oracle answers satisfy the runner's sole
measurability premise once the frame is measurable and the deterministic
parameterized derivative map is continuous. -/
theorem truncatedHiddenStageOracle_jointlyMeasurable
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (frame : Ω → Fin (N + 1) → E) (hframe : Measurable frame)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E p) (Metric.closedBall (0 : E) R) N)
    (stageOracle : (omega : Ω) → (t : Fin N) →
      ExactSymmetricJetOracle
        (ballVIData (E := E) p hp Lp hLp R hR)
        (truncatedHiddenOperator p profile Lp R N t.1 (frame omega)))
    (hcontinuous : TruncatedHiddenJetParameterContinuous
      (E := E) p profile Lp R N) :
    BorelStoppingPolicy.JointlyMeasurableStageOracle policy
      (fun omega t x => (stageOracle omega t).answer x) := by
  apply truncatedHiddenStageOracle_jointlyMeasurable_of_components
    p hp profile Lp hLp R hR N frame policy stageOracle
  intro t j
  have hall := truncatedHiddenJetComponents_jointlyMeasurable
    p profile Lp R N frame hframe hcontinuous t j
  have harg : Measurable
      (fun z : Ω × Metric.closedBall (0 : E) R => (z.1, z.2.1)) := by
    fun_prop
  convert hall.comp harg using 1 <;> rfl

/-- The canonical truncated exact oracles are jointly measurable, with no
remaining analytic premise. -/
theorem canonicalTruncatedHiddenStageOracle_jointlyMeasurable
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (frame : Ω → Fin (N + 1) → E) (hframe : Measurable frame)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E p) (Metric.closedBall (0 : E) R) N) :
    BorelStoppingPolicy.JointlyMeasurableStageOracle policy
      (fun omega t x =>
        (truncatedHiddenExactOracle p hp profile Lp hLp R hR N t
          (frame omega)).answer x) := by
  exact truncatedHiddenStageOracle_jointlyMeasurable
    p hp profile Lp hLp R hR N frame hframe policy
    (fun omega t => truncatedHiddenExactOracle
      p hp profile Lp hLp R hR N t (frame omega))
    (truncatedHiddenJetParameterContinuous_proved p profile Lp hR N)

/-- The executable Borel runner for the canonical truncated hidden oracle is
jointly measurable in frame randomness and policy seed. -/
theorem canonicalTruncatedHiddenJointlyMeasurableRunner
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (frame : Ω → Fin (N + 1) → E) (hframe : Measurable frame)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E p) (Metric.closedBall (0 : E) R) N)
    (fill : Metric.closedBall (0 : E) R) (dummy : SymmetricExactJet E p) :
    BorelStoppingPolicy.JointlyMeasurableRunner policy
      (fun omega t x =>
        (truncatedHiddenExactOracle p hp profile Lp hLp R hR N t
          (frame omega)).answer x) fill dummy := by
  apply BorelStoppingPolicy.jointlyMeasurableRunner_of_stageOracle
  exact canonicalTruncatedHiddenStageOracle_jointlyMeasurable
    p hp profile Lp hLp R hR N frame hframe policy

/-- Stage `t` of the canonical truncated oracle inspects only frame columns
`0,...,t`; hence the recursive runner is genuinely online. -/
theorem canonicalTruncatedHiddenStageOracle_prefix
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (frame : Ω → Fin (N + 1) → E) :
    BorelStoppingPolicy.StageOracleDependsOnFramePrefix frame
      (fun omega t x =>
        (truncatedHiddenExactOracle p hp profile Lp hLp R hR N t
          (frame omega)).answer x) := by
  intro t omega omega' hprefix x
  have hop : truncatedHiddenOperator p profile Lp R N t.1 (frame omega) =
      truncatedHiddenOperator p profile Lp R N t.1 (frame omega') := by
    apply truncatedHiddenOperator_congr_prefix p profile Lp R N t.1
      (Nat.le_of_lt t.2)
    intro i
    apply hprefix
    exact i.2
  funext j
  apply Subtype.ext
  change iteratedFDeriv ℝ j.1
      (truncatedHiddenOperator p profile Lp R N t.1 (frame omega)) x =
    iteratedFDeriv ℝ j.1
      (truncatedHiddenOperator p profile Lp R N t.1 (frame omega')) x
  rw [hop]

noncomputable def canonicalRunnerFixedSeedSimulation
    {N d : ℕ} {R : ℝ} (prior : SequentialFramePrior E N d R)
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (hframe : Measurable prior.frame)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E p) (Metric.closedBall (0 : E) R) N)
    (fill : Metric.closedBall (0 : E) R) (dummy : SymmetricExactJet E p)
    (seed : policy.Seed) : FixedSeedSimulation prior := by
  let stageOracle := fun omega t x =>
    (truncatedHiddenExactOracle p hp profile Lp hLp R hR N t
      (prior.frame omega)).answer x
  have hrunner : BorelStoppingPolicy.JointlyMeasurableRunner policy
      stageOracle fill dummy :=
    canonicalTruncatedHiddenJointlyMeasurableRunner
      p hp profile Lp hLp R hR N prior.frame hframe policy fill dummy
  have hprefix : BorelStoppingPolicy.StageOracleDependsOnFramePrefix
      prior.frame stageOracle :=
    canonicalTruncatedHiddenStageOracle_prefix
      p hp profile Lp hLp R hR N prior.frame
  refine
    { query := fun t omega =>
        (BorelStoppingPolicy.runnerQuery policy stageOracle fill dummy
          t (omega, seed)).1
      output := fun omega =>
        (BorelStoppingPolicy.runnerOutput policy stageOracle fill dummy
          (omega, seed)).1
      query_projection_measurable := ?_
      output_projection_measurable := ?_
      query_prefix := ?_
      output_prefix := ?_
      query_feasible := ?_
      output_feasible := ?_
      query_slab_measurable := ?_
      output_slab_measurable := ?_ }
  · intro t i
    have hq := (hrunner.query_joint t).comp
      (measurable_id.prodMk (measurable_const : Measurable (fun _ : prior.Omega => seed)))
    have hf : Measurable (fun omega => prior.frame omega i.castSucc) :=
      (measurable_pi_apply i.castSucc).comp hframe
    have hqe : Measurable (fun omega =>
        (BorelStoppingPolicy.runnerQuery policy stageOracle fill dummy
          t (omega, seed)).1) := measurable_subtype_coe.comp hq
    fun_prop
  · have ho := hrunner.output_joint.comp
      (measurable_id.prodMk (measurable_const : Measurable (fun _ : prior.Omega => seed)))
    have hf : Measurable (fun omega => prior.frame omega (Fin.last N)) :=
      (measurable_pi_apply (Fin.last N)).comp hframe
    have hoe : Measurable (fun omega =>
        (BorelStoppingPolicy.runnerOutput policy stageOracle fill dummy
          (omega, seed)).1) := measurable_subtype_coe.comp ho
    fun_prop
  · intro t
    exact BorelStoppingPolicy.runnerQuery_dependsOnlyOnFramePrefix
      policy prior.frame stageOracle fill dummy hprefix seed t
  · exact BorelStoppingPolicy.runnerOutput_dependsOnlyOnFramePrefix
      policy prior.frame stageOracle fill dummy hprefix seed
  · intro t omega
    have hm := (BorelStoppingPolicy.runnerQuery policy stageOracle fill dummy
      t (omega, seed)).2
    simpa only [Metric.mem_closedBall, dist_zero_right] using hm
  · intro omega
    have hm := (BorelStoppingPolicy.runnerOutput policy stageOracle fill dummy
      (omega, seed)).2
    simpa only [Metric.mem_closedBall, dist_zero_right] using hm
  · intro t i
    have hm : Measurable (fun omega => inner ℝ (prior.frame omega i.castSucc)
        ((BorelStoppingPolicy.runnerQuery policy stageOracle fill dummy
          t (omega, seed)).1)) := by
      have hq := (hrunner.query_joint t).comp
        (measurable_id.prodMk (measurable_const : Measurable (fun _ : prior.Omega => seed)))
      have hf : Measurable (fun omega => prior.frame omega i.castSucc) :=
        (measurable_pi_apply i.castSucc).comp hframe
      have hqe : Measurable (fun omega =>
          (BorelStoppingPolicy.runnerQuery policy stageOracle fill dummy
            t (omega, seed)).1) := measurable_subtype_coe.comp hq
      fun_prop
    exact measurableSet_Iic.preimage hm.abs
  · have hm : Measurable (fun omega => inner ℝ (prior.frame omega (Fin.last N))
        ((BorelStoppingPolicy.runnerOutput policy stageOracle fill dummy
          (omega, seed)).1)) := by
      have ho := hrunner.output_joint.comp
        (measurable_id.prodMk (measurable_const : Measurable (fun _ : prior.Omega => seed)))
      have hf : Measurable (fun omega => prior.frame omega (Fin.last N)) :=
        (measurable_pi_apply (Fin.last N)).comp hframe
      have hoe : Measurable (fun omega =>
          (BorelStoppingPolicy.runnerOutput policy stageOracle fill dummy
            (omega, seed)).1) := measurable_subtype_coe.comp ho
      fun_prop
    exact measurableSet_Iic.preimage hm.abs

/-- Joint measurability of the final hidden exact-oracle answer. -/
theorem finalHiddenOracle_jointlyMeasurable
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (frame : Ω → Fin (N + 1) → E) (hframe : Measurable frame)
    (oracle : ∀ omega,
      ExactSymmetricJetOracle
        (ballVIData (E := E) p hp Lp hLp R hR)
        (hiddenOperator p profile Lp R N (frame omega)))
    (hcontinuous : FinalHiddenJetParameterContinuous
      (E := E) p profile Lp R N) :
    Measurable (fun z : Ω × E => (oracle z.1).answer z.2) := by
  exact exactSymmetricJetOracle_answer_jointlyMeasurable
    (ballVIData (E := E) p hp Lp hLp R hR) oracle
    (fun j => finalHiddenJetComponents_jointlyMeasurable
      p profile Lp R N frame hframe hcontinuous j)

/-- The canonical final exact oracle is jointly measurable, with no remaining
analytic premise. -/
theorem canonicalFinalHiddenOracle_jointlyMeasurable
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (frame : Ω → Fin (N + 1) → E) (hframe : Measurable frame) :
    Measurable (fun z : Ω × E =>
      (finalHiddenExactOracle p hp profile Lp hLp R hR N
        (frame z.1)).answer z.2) := by
  exact finalHiddenOracle_jointlyMeasurable
    p hp profile Lp hLp R hR N frame hframe
    (fun omega => finalHiddenExactOracle
      p hp profile Lp hLp R hR N (frame omega))
    (finalHiddenJetParameterContinuous_proved p profile Lp hR N)

end ConcreteRunnerBridge

end VIReference.Pilot
