import VIReference.Pilot.UpperBorelBridge
import VIReference.Pilot.UpperBorelPrimitives

/-!
# Product-Borel outcomes for upper capped calls

This module connects the product-Borel certificate space used by the concrete
upper programs to the generic capped-policy compiler.
-/

namespace VIReference.Pilot

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace ExactJetProgram

variable {X Answer Output P : Type*}
  [MeasurableSpace X] [MeasurableSpace Answer]
  [MeasurableSpace Output] [MeasurableSpace P]

/-- Consume one answer when the program is querying; a terminal program stays
terminal.  The history query-point coordinate is intentionally irrelevant to
replay, so the companion theorem needs only an arbitrary fixed dummy point. -/
def afterFirstAnswer (program : ExactJetProgram X Answer Output)
    (answer : Answer) : ExactJetProgram X Answer Output :=
  match program with
  | .halt result => .halt result
  | .query _ next => next answer

/-- Joint outcome measurability passes to the continuation after its first
answer.  This is the induction step used by finite capped fallback trees. -/
theorem IsJointlyBorelOutcome.afterFirstAnswer
    {program : P → ExactJetProgram X Answer Output}
    (hprogram : IsJointlyBorelOutcome program) (dummy : X) :
    IsJointlyBorelOutcome (fun z : P × Answer =>
      afterFirstAnswer (program z.1) z.2) := by
  intro n
  have htail : Measurable (fun z : (P × Answer) ×
      (Fin n → X × Answer) =>
        Fin.cons (α := fun _ => X × Answer) (dummy, z.1.2) z.2) := by
    refine measurable_pi_lambda _ fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_const.prodMk (measurable_snd.comp measurable_fst)
    · exact (measurable_pi_apply j).comp measurable_snd
  have harg : Measurable (fun z : (P × Answer) ×
      (Fin n → X × Answer) =>
      (z.1.1, Fin.cons (α := fun _ => X × Answer)
        (dummy, z.1.2) z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk htail
  have hm := (hprogram (n + 1)).comp harg
  convert hm using 1
  funext z
  cases hprog : program z.1.1 with
  | halt result =>
      simp only [Function.comp_apply]
      rw [hprog]
      simp [ExactJetProgram.afterFirstAnswer, replayOutcomeAction,
        residualAfterHistory, residualAfterAnswers]
  | query point next =>
      simp only [Function.comp_apply]
      rw [hprog]
      simpa [ExactJetProgram.afterFirstAnswer] using
        (replayOutcomeAction_query_succ point next
          (Fin.cons (α := fun _ => X × Answer)
            (dummy, z.1.2) z.2)).symm

/-- Mapping a successful terminal value by the identity does not change an
exact program. -/
theorem bind_halt_some_id (program : ExactJetProgram X Answer Output) :
    program.bind (fun value => .halt (some value)) = program := by
  induction program with
  | halt result => cases result <;> rfl
  | query point next ih =>
      simp only [ExactJetProgram.bind]
      congr
      funext answer
      exact ih answer

/-- Two query-free terminal maps fuse.  This is the transport law used when
two nested `withStart` adapters are collapsed. -/
theorem bind_halt_some_comp {A B C : Type*}
    (program : ExactJetProgram X Answer A) (f : A → B) (g : B → C) :
    (program.bind (fun value => .halt (some (f value)))).bind
        (fun value => .halt (some (g value))) =
      program.bind (fun value => .halt (some (g (f value)))) := by
  induction program with
  | halt result => cases result <;> rfl
  | query point next ih =>
      simp only [ExactJetProgram.bind]
      congr
      funext answer
      exact ih answer

/-- A query-free map of successful terminal values distributes through the
explicit-failure fallback combinator. -/
theorem orElse_bind_halt_some {A B : Type*}
    (first fallback : ExactJetProgram X Answer A) (f : A → B) :
    (first.orElse fallback).bind
        (fun value => .halt (some (f value))) =
      (first.bind (fun value => .halt (some (f value)))).orElse
        (fallback.bind (fun value => .halt (some (f value)))) := by
  induction first with
  | halt result => cases result <;> rfl
  | query point next ih =>
      simp only [ExactJetProgram.orElse, ExactJetProgram.bind]
      congr
      funext answer
      exact ih answer

/-- A query-free successful-output map commutes with installation of a local
hard cap.  No fuel is reset because the terminal map performs no query. -/
theorem locallyCapped_bind_halt_some {A B : Type*}
    (program : ExactJetProgram X Answer A) (f : A → B) (cap : ℕ) :
    (program.bind (fun value => .halt (some (f value)))).locallyCapped cap =
      (program.locallyCapped cap).bind
        (fun value => .halt (some (f value))) := by
  induction cap generalizing program with
  | zero =>
      cases program with
      | halt result => cases result <;> rfl
      | query point next => rfl
  | succ cap ih =>
      cases program with
      | halt result => cases result <;> rfl
      | query point next =>
          simp only [ExactJetProgram.bind, ExactJetProgram.locallyCapped]
          congr
          funext answer
          exact ih (next answer)

/-- Compiling answers commutes with a query-free map of successful terminal
values. -/
theorem mapAnswers_bind_halt_some {Answer₁ Answer₂ A B : Type*}
    (program : ExactJetProgram X Answer₂ A)
    (transform : X → Answer₁ → Answer₂) (f : A → B) :
    (program.mapAnswers transform).bind
        (fun value => .halt (some (f value))) =
      (program.bind (fun value => .halt (some (f value)))).mapAnswers
        transform := by
  induction program with
  | halt result => cases result <;> rfl
  | query point next ih =>
      simp only [ExactJetProgram.mapAnswers, ExactJetProgram.bind]
      congr
      funext answer
      exact ih (transform point answer)

/-- Answer compilation commutes with installing a fixed local cap. -/
theorem mapAnswers_locallyCapped {Answer₁ Answer₂ A : Type*}
    (program : ExactJetProgram X Answer₂ A)
    (transform : X → Answer₁ → Answer₂) (cap : ℕ) :
    (program.mapAnswers transform).locallyCapped cap =
      (program.locallyCapped cap).mapAnswers transform := by
  induction cap generalizing program with
  | zero => cases program <;> rfl
  | succ cap ih =>
      cases program with
      | halt result => rfl
      | query point next =>
          simp only [ExactJetProgram.mapAnswers, ExactJetProgram.locallyCapped]
          congr
          funext answer
          exact ih (next (transform point answer))

/-- Combined conjugation law used by anchored regularized subcalls: transport
the successful certificate after compiling and capping, or transport first
and then compile the oracle answers. -/
theorem locallyCapped_mapAnswers_bind_halt_some
    {Answer₁ Answer₂ A B : Type*}
    [MeasurableSpace Answer₁] [MeasurableSpace Answer₂]
    (program : ExactJetProgram X Answer₂ A)
    (transform : X → Answer₁ → Answer₂) (f : A → B) (cap : ℕ) :
    ((program.mapAnswers transform).locallyCapped cap).bind
        (fun value => .halt (some (f value))) =
      ExactJetProgram.mapAnswers transform
        ((program.bind (fun value => .halt (some (f value)))).locallyCapped cap) := by
  rw [← ExactJetProgram.locallyCapped_bind_halt_some,
    ExactJetProgram.mapAnswers_bind_halt_some,
    ExactJetProgram.mapAnswers_locallyCapped]

end ExactJetProgram

/-- Replacing an already replaced public start point keeps only the most
recent anchor.  All oracle-domain and jet-order fields remain definitionally
unchanged. -/
@[simp] theorem VIPublicData.withStart_withStart
    (data : VIPublicData E) (first second : data.X) :
    (data.withStart first).withStart second = data.withStart second := by
  rfl

/-- The explicit certificate transport is functorial across two successive
changes of public start point. -/
@[simp] theorem EvaluatedNormalCertificate.fromWithStart_fromWithStart
    (data : VIPublicData E) (first second : data.X)
    (cert : EvaluatedNormalCertificate
      ((data.withStart first).withStart second)) :
    (cert.fromWithStart (data.withStart first) second).fromWithStart data first =
      cert.fromWithStart data second := by
  rfl

local instance upperCertificateMeasurableSpace (data : VIPublicData E) :
    MeasurableSpace (EvaluatedNormalCertificate data) :=
  upperEvaluatedNormalCertificateMeasurableSpace data

/-- The program actually observed when a call is installed as a child of
another upper algorithm.  Keeping the cap in this definition is essential:
for a varying family of calls, measurability of the raw programs says nothing
about a center-dependent natural-valued cap. -/
def CappedExactJetCall.installedProgram (data : VIPublicData E)
    (call : CappedExactJetCall data) :=
  call.program.locallyCapped call.cap

/-- Transport a call made after replacing the public start point back to one
fixed certificate/query type, then install its actual cap.  This is the
common-codomain observable used for joint measurability in the start point. -/
def CappedExactJetCall.anchoredInstalledProgram (data : VIPublicData E)
    (anchor : data.X) (call : CappedExactJetCall (data.withStart anchor)) :=
  (call.fromWithStart data anchor).installedProgram data

/-- Transporting a call through two successive anchors is exactly the same
query program, cap, and terminal certificate map as transporting directly
through the last anchor. -/
theorem CappedExactJetCall.fromWithStart_fromWithStart
    (data : VIPublicData E) (first second : data.X)
    (call : CappedExactJetCall
      ((data.withStart first).withStart second)) :
    (call.fromWithStart (data.withStart first) second).fromWithStart data first =
      call.fromWithStart data second := by
  cases call with
  | mk cap program =>
      change CappedExactJetCall.mk cap _ = CappedExactJetCall.mk cap _
      rw [CappedExactJetCall.mk.injEq]
      refine ⟨rfl, ?_⟩
      change
        (program.bind (fun cert => .halt (some
          (cert.fromWithStart (data.withStart first) second)))).bind
            (fun cert => .halt (some (cert.fromWithStart data first))) =
          program.bind (fun cert => .halt (some
            (cert.fromWithStart data second)))
      simpa only [VIPublicData.withStart,
        EvaluatedNormalCertificate.fromWithStart] using
        ExactJetProgram.bind_halt_some_comp program
          (fun cert => cert.fromWithStart (data.withStart first) second)
          (fun cert => cert.fromWithStart data first)

/-- Full outcome measurability of the *installed* call. -/
def CappedExactJetCall.HasBorelCappedOutcome
    (data : VIPublicData E) (call : CappedExactJetCall data) : Prop :=
  call.installedProgram data |>.IsBorelOutcome

/-- Strong, compositional Borel datum for a call: every fixed transcript
reveals measurably whether the program has returned a full certificate or is
requesting its next feasible query. -/
def CappedExactJetCall.HasBorelOutcome
    (data : VIPublicData E) (call : CappedExactJetCall data) : Prop :=
  @ExactJetProgram.IsBorelOutcome data.X (SymmetricExactJet E data.p)
    (EvaluatedNormalCertificate data) inferInstance inferInstance
    (upperEvaluatedNormalCertificateMeasurableSpace data) call.program

/-- The compiler's total certificate projection is measurable for the exact
product-Borel structure used to prove concrete program outcomes measurable. -/
theorem measurable_certifiedCallOutput_upper
    (data : VIPublicData E) (fallback : data.X) :
    Measurable (certifiedCallOutput data fallback) := by
  have hpoint := measurable_evaluatedNormalCertificate_point data
  rw [← upperFeasible_measurable_eq_normBorel data] at hpoint
  have h := measurable_option_elim fallback
    (EvaluatedNormalCertificate.point :
      EvaluatedNormalCertificate data → data.X) hpoint
  convert h using 1
  funext value
  cases value <;> rfl

/-- Any concrete call whose uncapped terminal certificate/query observation
is Borel satisfies the compiler's exact every-prefix condition. -/
theorem CappedExactJetCall.isBorel_of_upperOutcome
    (data : VIPublicData E) (call : CappedExactJetCall data)
    (fallback : data.X) (hprogram : call.program.IsBorelOutcome) :
    call.IsBorel data fallback :=
  call.isBorel_of_isBorelOutcome data fallback hprogram
    (measurable_certifiedCallOutput_upper data fallback)

theorem CappedExactJetCall.HasBorelOutcome.isBorel
    (data : VIPublicData E) (call : CappedExactJetCall data)
    (hcall : call.HasBorelOutcome data) (fallback : data.X) :
    call.IsBorel data fallback :=
  call.isBorel_of_upperOutcome data fallback hcall

/-- Installed-outcome measurability is already exactly the condition needed
by the policy compiler; no measurability assertion about the uncapped syntax
tree is required. -/
theorem CappedExactJetCall.HasBorelCappedOutcome.isBorel
    (data : VIPublicData E) (call : CappedExactJetCall data)
    (hcall : call.HasBorelCappedOutcome data) (fallback : data.X) :
    call.IsBorel data fallback := by
  intro n
  exact hcall.isBorelAction (certifiedCallOutput data fallback)
    (measurable_certifiedCallOutput_upper data fallback) n.1

/-- Compositional outcome property for every call chosen by a residual
family.  It is intentionally stronger than `IsBorel`: boost and restart use
returned normal/value fields to select later measurable branches. -/
def ResidualSolverFamily.HasBorelOutcome {p : ℕ}
    (family : ResidualSolverFamily.{u} p) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (data : VIPublicData E) (hp : data.p = p) (center : data.X)
    (R epsilon : ℝ),
      ((family.atData data hp).solve center R epsilon).HasBorelOutcome data

def StrongSolverFamily.HasBorelOutcome {p : ℕ}
    (family : StrongSolverFamily.{u} p) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (data : VIPublicData E) (hp : data.p = p) (center : data.X)
    (mu delta : ℝ),
      ((family.atData data hp).solve center mu delta).HasBorelOutcome data

/-- Joint residual-family invariant.  Parameters may be chosen measurably
from a previous certificate, so pointwise measurability is not sufficient for
boost/restart composition.  The two scalar parameters remain fixed public
inputs; only the center and transcript are required jointly measurable. -/
def ResidualSolverFamily.HasJointBorelOutcome {p : ℕ}
    (family : ResidualSolverFamily.{u} p) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome
        (fun center : data.X =>
          ((family.atData data hp).solve center R epsilon).program)

/-- Joint strong-family invariant in the center, for each fixed public
`(mu, delta)`. -/
def StrongSolverFamily.HasJointBorelOutcome {p : ℕ}
    (family : StrongSolverFamily.{u} p) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome
        (fun center : data.X =>
          ((family.atData data hp).solve center mu delta).program)

/-- Capped compositional invariant for a residual family.

The first clause is joint measurability of the actual installed call for one
fixed public datum.  The second is the additional anchor-uniform clause needed
by boost: the public datum may be replaced by `data.withStart anchor`, while
the solve center also varies.  `fromWithStart` gives all outcomes one fixed
certificate type before measurability is asserted.  The scalar inputs remain
fixed in both clauses. -/
def ResidualSolverFamily.HasJointBorelCappedOutcome {p : ℕ}
    (family : ResidualSolverFamily.{u} p) : Prop :=
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
      (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome
        (fun center : data.X =>
          let call := (family.atData data hp).solve center R epsilon
          call.installedProgram data)) ∧
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
      (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome
        (fun state : data.X × data.X =>
          let shifted := data.withStart state.1
          let call := (family.atData shifted hp).solve state.2 R epsilon
          call.anchoredInstalledProgram data state.1))

/-- Capped anchor-uniform invariant for a strong family, with fixed
`(mu, delta)`. -/
def StrongSolverFamily.HasJointBorelCappedOutcome {p : ℕ}
    (family : StrongSolverFamily.{u} p) : Prop :=
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
      (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome
        (fun center : data.X =>
          let call := (family.atData data hp).solve center mu delta
          call.installedProgram data)) ∧
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
      (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ),
      ExactJetProgram.IsJointlyBorelOutcome
        (fun state : data.X × data.X =>
          let shifted := data.withStart state.1
          let call := (family.atData shifted hp).solve state.2 mu delta
          call.anchoredInstalledProgram data state.1))

theorem ResidualSolverFamily.HasJointBorelCappedOutcome.ordinary
    {p : ℕ} {family : ResidualSolverFamily.{u} p}
    (hfamily : family.HasJointBorelCappedOutcome)
    (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (fun center : data.X =>
        let call := (family.atData data hp).solve center R epsilon
        call.installedProgram data) :=
  hfamily.1 E data hp R epsilon

theorem ResidualSolverFamily.HasJointBorelCappedOutcome.anchored
    {p : ℕ} {family : ResidualSolverFamily.{u} p}
    (hfamily : family.HasJointBorelCappedOutcome)
    (data : VIPublicData E) (hp : data.p = p) (R epsilon : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (fun state : data.X × data.X =>
        let shifted := data.withStart state.1
        let call := (family.atData shifted hp).solve state.2 R epsilon
        call.anchoredInstalledProgram data state.1) :=
  hfamily.2 E data hp R epsilon

theorem StrongSolverFamily.HasJointBorelCappedOutcome.ordinary
    {p : ℕ} {family : StrongSolverFamily.{u} p}
    (hfamily : family.HasJointBorelCappedOutcome)
    (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (fun center : data.X =>
        let call := (family.atData data hp).solve center mu delta
        call.installedProgram data) :=
  hfamily.1 E data hp mu delta

theorem StrongSolverFamily.HasJointBorelCappedOutcome.anchored
    {p : ℕ} {family : StrongSolverFamily.{u} p}
    (hfamily : family.HasJointBorelCappedOutcome)
    (data : VIPublicData E) (hp : data.p = p) (mu delta : ℝ) :
    ExactJetProgram.IsJointlyBorelOutcome
      (fun state : data.X × data.X =>
        let shifted := data.withStart state.1
        let call := (family.atData shifted hp).solve state.2 mu delta
        call.anchoredInstalledProgram data state.1) :=
  hfamily.2 E data hp mu delta

theorem ResidualSolverFamily.HasJointBorelCappedOutcome.isBorel
    {p : ℕ} {family : ResidualSolverFamily.{u} p}
    (hfamily : family.HasJointBorelCappedOutcome) : family.IsBorel := by
  intro E _ _ _ _ _ data hp center R epsilon
  let call := (family.atData data hp).solve center R epsilon
  have hcall : call.HasBorelCappedOutcome data :=
    (hfamily.1 E data hp R epsilon).fixed center
  exact hcall.isBorel data call center

theorem StrongSolverFamily.HasJointBorelCappedOutcome.isBorel
    {p : ℕ} {family : StrongSolverFamily.{u} p}
    (hfamily : family.HasJointBorelCappedOutcome) : family.IsBorel := by
  intro E _ _ _ _ _ data hp center mu delta
  let call := (family.atData data hp).solve center mu delta
  have hcall : call.HasBorelCappedOutcome data :=
    (hfamily.1 E data hp mu delta).fixed center
  exact hcall.isBorel data call center

theorem ResidualSolverFamily.HasJointBorelOutcome.hasBorelOutcome
    {p : ℕ} {family : ResidualSolverFamily.{u} p}
    (hfamily : family.HasJointBorelOutcome) : family.HasBorelOutcome := by
  intro E _ _ _ _ _ data hp center R epsilon
  exact (hfamily E data hp R epsilon).fixed center

theorem StrongSolverFamily.HasJointBorelOutcome.hasBorelOutcome
    {p : ℕ} {family : StrongSolverFamily.{u} p}
    (hfamily : family.HasJointBorelOutcome) : family.HasBorelOutcome := by
  intro E _ _ _ _ _ data hp center mu delta
  exact (hfamily E data hp mu delta).fixed center

theorem ResidualSolverFamily.HasBorelOutcome.isBorel {p : ℕ}
    {family : ResidualSolverFamily.{u} p}
    (hfamily : family.HasBorelOutcome) : family.IsBorel := by
  intro E _ _ _ _ _ data hp center R epsilon
  exact (hfamily E data hp center R epsilon).isBorel data _ center

theorem StrongSolverFamily.HasBorelOutcome.isBorel {p : ℕ}
    {family : StrongSolverFamily.{u} p}
    (hfamily : family.HasBorelOutcome) : family.IsBorel := by
  intro E _ _ _ _ _ data hp center mu delta
  exact (hfamily E data hp center mu delta).isBorel data _ center

theorem ResidualSolverFamily.HasJointBorelOutcome.isBorel
    {p : ℕ} {family : ResidualSolverFamily.{u} p}
    (hfamily : family.HasJointBorelOutcome) : family.IsBorel :=
  hfamily.hasBorelOutcome.isBorel

theorem StrongSolverFamily.HasJointBorelOutcome.isBorel
    {p : ℕ} {family : StrongSolverFamily.{u} p}
    (hfamily : family.HasJointBorelOutcome) : family.IsBorel :=
  hfamily.hasBorelOutcome.isBorel

end

end VIReference.Pilot
