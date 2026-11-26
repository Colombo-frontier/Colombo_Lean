import VIReference.Pilot.RandomExecution

/-!
# Executable Borel stopping-policy runner

This module supplies the operational object missing from the randomized
lower-bound bridge.  The fixed-length state is only a representation: its
`stopped` flag ensures that neither a policy rule nor an oracle answer after
the first stop is consulted when defining the saved output and genuine
history prefix.
-/

open Set MeasureTheory

namespace VIReference.Pilot

namespace BorelStoppingPolicy

section Runner

variable {Ω E Answer : Type*} [MeasurableSpace Ω]
  [MeasurableSpace E] [MeasurableSpace Answer]
  {X : Set E} {budget : ℕ}

/-- A fixed-index state after `n` representation steps.  The Boolean records
whether a genuine stop has occurred; the natural number and feasible point
then store its call count and saved output. -/
abbrev RunnerState (X : Set E) (Answer : Type*) (n : ℕ) :=
  OracleHistory X Answer n × Bool × ℕ × X

/-- Append one representation entry to a fixed finite history. -/
def runnerSnoc {n : ℕ} (history : OracleHistory X Answer n)
    (entry : X × Answer) : OracleHistory X Answer (n + 1) :=
  Fin.lastCases entry history

@[simp] theorem runnerSnoc_castSucc {n : ℕ}
    (history : OracleHistory X Answer n) (entry : X × Answer) (i : Fin n) :
    runnerSnoc history entry i.castSucc = history i := by
  simp [runnerSnoc]

@[simp] theorem runnerSnoc_last {n : ℕ}
    (history : OracleHistory X Answer n) (entry : X × Answer) :
    runnerSnoc history entry (Fin.last n) = entry := by
  simp [runnerSnoc]

@[simp] theorem restrict_self {n : ℕ} (history : OracleHistory X Answer n)
    (hn : n ≤ n) : OracleHistory.restrict history hn = history := by
  funext i
  rfl

@[simp] theorem restrict_restrict {l m n : ℕ}
    (history : OracleHistory X Answer n) (hmn : m ≤ n) (hlm : l ≤ m) :
    OracleHistory.restrict (OracleHistory.restrict history hmn) hlm =
      OracleHistory.restrict history (Nat.le_trans hlm hmn) := by
  rfl

/-- Initial running state with empty history. -/
def runnerInitial (fill : X) : RunnerState X Answer 0 :=
  (fun i => Fin.elim0 i, false, 0, fill)

/-- One fixed-index representation step.  If the run has stopped, only the
fixed filler is appended; no later policy rule is evaluated. -/
def runnerStep
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (t : ℕ) (ht : t < budget) (z : Ω × policy.Seed)
    (state : RunnerState X Answer t) : RunnerState X Answer (t + 1) :=
  if state.2.1 then
    (runnerSnoc state.1 (fill, dummy), state.2)
  else
    match policy.rule ⟨t, Nat.lt_succ_of_lt ht⟩ (z.2, state.1) with
    | Sum.inl output =>
        (runnerSnoc state.1 (fill, dummy), true, t, output)
    | Sum.inr query =>
        (runnerSnoc state.1
          (query, stageOracle z.1 ⟨t, ht⟩ query.1), false, 0, fill)

/-- State after `n≤budget` fixed-index representation steps. -/
def runnerState
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer) :
    (n : ℕ) → n ≤ budget → Ω × policy.Seed → RunnerState X Answer n
  | 0, _, _ => runnerInitial fill
  | n + 1, hn, z =>
      runnerStep policy stageOracle fill dummy n (by omega) z
        (runnerState policy stageOracle fill dummy n (by omega) z)

/-- The query exposed at fixed index `t`.  It is the actual query while the
run is active and the fixed feasible filler after stopping. -/
def runnerQuery
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (t : Fin budget) (z : Ω × policy.Seed) : X :=
  let state := runnerState policy stageOracle fill dummy t.1 (Nat.le_of_lt t.2) z
  if state.2.1 then fill else
    match policy.rule ⟨t.1, Nat.lt_succ_of_lt t.2⟩ (z.2, state.1) with
    | Sum.inl _ => fill
    | Sum.inr query => query

/-- Saved feasible output at the cap.  The cap rule is used only if no earlier
stop occurred.  Its impossible query branch is assigned the filler; the
`cap_stops` theorem below proves that branch cannot occur. -/
def runnerOutput
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (z : Ω × policy.Seed) : X :=
  let state := runnerState policy stageOracle fill dummy budget le_rfl z
  if state.2.1 then state.2.2.2 else
    match policy.rule ⟨budget, Nat.lt_succ_self budget⟩ (z.2, state.1) with
    | Sum.inl output => output
    | Sum.inr _ => fill

/-- Number of actual calls before the saved output. -/
def runnerStoppedAt
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (z : Ω × policy.Seed) : ℕ :=
  let state := runnerState policy stageOracle fill dummy budget le_rfl z
  if state.2.1 then state.2.2.1 else budget

/-- Fixed-cap representation history.  Its prefix of length
`runnerStoppedAt` is the genuine run; later entries are ignored. -/
def runnerHistory
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (z : Ω × policy.Seed) : OracleHistory X Answer budget :=
  (runnerState policy stageOracle fill dummy budget le_rfl z).1

/-- Inductive semantic invariant of the executable state. -/
def RunnerStateValid
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (omega : Ω) (seed : policy.Seed)
    (t : ℕ) (ht : t ≤ budget) (state : RunnerState X Answer t) : Prop :=
  if state.2.1 then
    ∃ n, ∃ hn : n ≤ t,
      state.2.2.1 = n ∧
      policy.IsUnpaddedStageRun (stageOracle omega) seed n
        (Nat.le_trans hn ht) (OracleHistory.restrict state.1 hn) state.2.2.2
  else
    policy.IsStageRunPrefix (stageOracle omega) seed t ht state.1

theorem runnerInitial_valid
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (omega : Ω) (seed : policy.Seed)
    (fill : X) :
    RunnerStateValid policy stageOracle omega seed 0 (Nat.zero_le _)
      (runnerInitial fill) := by
  simp [RunnerStateValid, runnerInitial,
    BorelStoppingPolicy.IsStageRunPrefix]

/-- Restricting below the old length discards the entry appended by a
representation step. -/
@[simp] theorem restrict_runnerSnoc {n t : ℕ} (history : OracleHistory X Answer t)
    (entry : X × Answer) (hnew : n ≤ t + 1) (hold : n ≤ t) :
    OracleHistory.restrict (runnerSnoc history entry) hnew =
      OracleHistory.restrict history hold := by
  funext i
  rw [OracleHistory.restrict, OracleHistory.restrict]
  have hi : (⟨i.1, lt_of_lt_of_le i.2
      hnew⟩ : Fin (t + 1)) =
      (⟨i.1, lt_of_lt_of_le i.2 hold⟩ : Fin t).castSucc := Fin.ext rfl
  rw [hi, runnerSnoc_castSucc]

/-- One executable step preserves the exact stopped-prefix invariant. -/
theorem runnerStep_valid
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (t : ℕ) (ht : t < budget) (z : Ω × policy.Seed)
    (state : RunnerState X Answer t)
    (hvalid : RunnerStateValid policy stageOracle z.1 z.2 t ht.le state) :
    RunnerStateValid policy stageOracle z.1 z.2 (t + 1) (Nat.succ_le_of_lt ht)
      (runnerStep policy stageOracle fill dummy t ht z state) := by
  by_cases hstopped : state.2.1
  · simp only [runnerStep, hstopped, if_pos, RunnerStateValid]
    rw [RunnerStateValid, if_pos hstopped] at hvalid
    obtain ⟨n, hn, hcount, hrun⟩ := hvalid
    refine ⟨n, hn.trans (Nat.le_succ t), hcount, ?_⟩
    have hhist : OracleHistory.restrict
        (runnerSnoc state.1 (fill, dummy))
          (hn.trans (Nat.le_succ t)) =
        OracleHistory.restrict state.1 hn :=
      restrict_runnerSnoc state.1 _ _ hn
    rw [hhist]
    convert hrun
  · rw [RunnerStateValid, if_neg hstopped] at hvalid
    simp only [runnerStep, hstopped, if_false]
    cases haction : policy.rule ⟨t, Nat.lt_succ_of_lt ht⟩ (z.2, state.1) with
    | inl output =>
        simp only [RunnerStateValid]
        rw [if_pos (by simp)]
        simp only [Bool.false_eq_true, if_false]
        refine ⟨t, Nat.le_succ t, rfl, ?_⟩
        have hhist : OracleHistory.restrict
            (runnerSnoc state.1 (fill, dummy))
              (Nat.le_succ t) = state.1 := by
          rw [restrict_runnerSnoc state.1 _ _ le_rfl, restrict_self]
        refine ⟨?_, ?_⟩
        · rw [hhist]
          exact hvalid
        · rw [hhist]
          simpa using haction
    | inr query =>
        simp only [RunnerStateValid]
        rw [if_neg (by simp)]
        simp only [Bool.false_eq_true, if_false]
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · constructor
          · simpa [runnerSnoc] using haction
          · simp [runnerSnoc]
        · have hj := hvalid j
          have hhist : OracleHistory.restrict
              (runnerSnoc state.1
                (query, stageOracle z.1 ⟨t, ht⟩ query.1))
                (Nat.le_of_lt j.castSucc.2) =
              OracleHistory.restrict state.1 (Nat.le_of_lt j.2) :=
            restrict_runnerSnoc state.1 _ _ _
          rw [hhist, runnerSnoc_castSucc]
          simpa only [Fin.coe_castSucc] using hj

/-- Every recursively computed state satisfies the stopped-prefix invariant. -/
theorem runnerState_valid
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (n : ℕ) (hn : n ≤ budget) (z : Ω × policy.Seed) :
    RunnerStateValid policy stageOracle z.1 z.2 n hn
      (runnerState policy stageOracle fill dummy n hn z) := by
  induction n with
  | zero => exact runnerInitial_valid policy stageOracle z.1 z.2 fill
  | succ n ih =>
      exact runnerStep_valid policy stageOracle fill dummy n (by omega) z _
        (ih (by omega))

/-- The runner's saved output and stopped prefix form an actual stage-oracle
execution with at most `budget` calls. -/
theorem runner_executes_unpadded_stage
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (z : Ω × policy.Seed) :
    ∃ n, ∃ hn : n ≤ budget,
      n = runnerStoppedAt policy stageOracle fill dummy z ∧
      policy.IsUnpaddedStageRun (stageOracle z.1) z.2 n hn
        (OracleHistory.restrict (runnerHistory policy stageOracle fill dummy z) hn)
        (runnerOutput policy stageOracle fill dummy z) := by
  let state := runnerState policy stageOracle fill dummy budget le_rfl z
  have hvalid := runnerState_valid policy stageOracle fill dummy budget le_rfl z
  change RunnerStateValid policy stageOracle z.1 z.2 budget le_rfl state at hvalid
  by_cases hs : state.2.1
  · rw [RunnerStateValid, if_pos hs] at hvalid
    obtain ⟨n, hn, hcount, hrun⟩ := hvalid
    have hstop : runnerStoppedAt policy stageOracle fill dummy z = n := by
      simp [runnerStoppedAt, state, hs, hcount]
    refine ⟨n, hn, hstop.symm, ?_⟩
    simpa [runnerHistory, runnerOutput, state, hs] using hrun
  · rw [RunnerStateValid, if_neg hs] at hvalid
    obtain ⟨output, hcap⟩ := policy.cap_stops (z.2, state.1)
    have hout : runnerOutput policy stageOracle fill dummy z = output := by
      simp [runnerOutput, state, hs, hcap]
    have hcount : runnerStoppedAt policy stageOracle fill dummy z = budget := by
      simp [runnerStoppedAt, state, hs]
    refine ⟨budget, le_rfl, hcount.symm, ?_⟩
    rw [hout]
    refine ⟨?_, ?_⟩
    · change policy.IsStageRunPrefix (stageOracle z.1) z.2 budget le_rfl state.1
      convert hvalid
    · change policy.rule ⟨budget, Nat.lt_succ_self budget⟩
        (z.2, state.1) = Sum.inl output
      simpa using hcap

/-- If every stage answer agrees with one fixed oracle (in particular, if a
slab-coupling theorem proves this along the run), the executable history is a
genuine exact-oracle history with the same saved output. -/
theorem runner_executes_fixedOracle_of_coupled
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer)
    (fixedOracle : Ω → E → Answer) (fill : X) (dummy : Answer)
    (z : Ω × policy.Seed)
    (hcouple : ∀ t x, stageOracle z.1 t x = fixedOracle z.1 x) :
    ∃ n, ∃ hn : n ≤ budget,
      n = runnerStoppedAt policy stageOracle fill dummy z ∧
      policy.IsUnpaddedRun (fixedOracle z.1) z.2 n hn
        (OracleHistory.restrict (runnerHistory policy stageOracle fill dummy z) hn)
        (runnerOutput policy stageOracle fill dummy z) := by
  obtain ⟨n, hn, hcount, hrun⟩ :=
    runner_executes_unpadded_stage policy stageOracle fill dummy z
  refine ⟨n, hn, hcount, ?_⟩
  exact hrun.to_fixedOracle (fun i => hcouple _ _)

/-- Fixed-cap padding of the runner's actual stopped execution is semantically
equivalent and preserves its saved output.  The padded suffix is produced by
`OracleHistory.pad`; it is not evaluated by `runnerStep` as an algorithmic
query. -/
theorem runner_executes_padded_fixedOracle_of_coupled
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer)
    (fixedOracle : Ω → E → Answer) (fill : X) (dummy : Answer)
    (z : Ω × policy.Seed)
    (hcouple : ∀ t x, stageOracle z.1 t x = fixedOracle z.1 x) :
    ∃ history : OracleHistory X Answer budget,
      policy.IsPaddedRun (fixedOracle z.1) z.2 history
        (runnerOutput policy stageOracle fill dummy z) := by
  apply (policy.unpadded_iff_padded (fixedOracle z.1) z.2 fill
    (runnerOutput policy stageOracle fill dummy z)).mp
  obtain ⟨n, hn, _hcount, hrun⟩ :=
    runner_executes_fixedOracle_of_coupled policy stageOracle fixedOracle fill dummy z hcouple
  exact ⟨n, hn,
    OracleHistory.restrict (runnerHistory policy stageOracle fill dummy z) hn, hrun⟩

theorem runnerState_history_restrict
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (m n : ℕ) (hnm : n ≤ m) (hm : m ≤ budget) (z : Ω × policy.Seed) :
    OracleHistory.restrict
      (runnerState policy stageOracle fill dummy m hm z).1 hnm =
      (runnerState policy stageOracle fill dummy n (hnm.trans hm) z).1 := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      rfl
  | succ m ih =>
      by_cases hnm' : n = m + 1
      · subst n
        congr
      · have hle : n ≤ m := by omega
        rw [runnerState]
        have hrest : OracleHistory.restrict
            (runnerStep policy stageOracle fill dummy m (by omega) z
              (runnerState policy stageOracle fill dummy m (by omega) z)).1 hnm =
            OracleHistory.restrict
              (runnerState policy stageOracle fill dummy m (by omega) z).1 hle := by
          simp only [runnerStep]
          split
          · apply restrict_runnerSnoc
          · split <;> apply restrict_runnerSnoc
        rw [hrest]
        exact ih hle (by omega)

theorem runnerHistory_query_eq_runnerQuery
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (t : Fin budget) (z : Ω × policy.Seed) :
    ((runnerHistory policy stageOracle fill dummy z) t).1 =
      runnerQuery policy stageOracle fill dummy t z := by
  let state := runnerState policy stageOracle fill dummy t.1
    (Nat.le_of_lt t.2) z
  have hp := congrFun (runnerState_history_restrict policy stageOracle fill dummy
    budget (t.1 + 1) (Nat.succ_le_iff.mpr t.2) le_rfl z) (Fin.last t.1)
  have hp' : (runnerHistory policy stageOracle fill dummy z t).1 =
      ((runnerState policy stageOracle fill dummy (t.1 + 1)
        (Nat.succ_le_iff.mpr t.2) z).1 (Fin.last t.1)).1 := by
    simpa [runnerHistory, OracleHistory.restrict] using congrArg (fun q => q.1) hp
  rw [hp']
  simp only [runnerState]
  change ((runnerStep policy stageOracle fill dummy t.1 t.2 z state).1
      (Fin.last t.1)).1 = _
  simp only [runnerStep]
  by_cases hs : state.2.1
  · simp [hs, runnerQuery, state, runnerSnoc_last]
  · simp only [hs, ↓reduceIte]
    cases haction : policy.rule ⟨t.1, Nat.lt_succ_of_lt t.2⟩ (z.2, state.1) <;>
      simp [runnerQuery, state, hs, haction, runnerSnoc_last]

/-- Two stage-oracle runners have identical states whenever their answers
agree at every query actually exposed by the first runner.  No agreement is
required at counterfactual points or after stopping. -/
theorem runnerState_eq_of_answerAtRunnerQuery
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle₁ stageOracle₂ : Ω → Fin budget → E → Answer)
    (fill : X) (dummy : Answer) (z : Ω × policy.Seed)
    (hanswer : ∀ t : Fin budget,
      stageOracle₁ z.1 t
          (runnerQuery policy stageOracle₁ fill dummy t z).1 =
        stageOracle₂ z.1 t
          (runnerQuery policy stageOracle₁ fill dummy t z).1)
    (n : ℕ) (hn : n ≤ budget) :
    runnerState policy stageOracle₁ fill dummy n hn z =
      runnerState policy stageOracle₂ fill dummy n hn z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprev := ih (by omega)
      rw [runnerState, runnerState, ← hprev]
      let state := runnerState policy stageOracle₁ fill dummy n (by omega) z
      simp only [runnerStep]
      by_cases hs : state.2.1
      · simp [state, hs]
      · simp only [state, hs]
        have hq : ∀ q,
            policy.rule ⟨n, by omega⟩ (z.2, state.1) = Sum.inr q →
            stageOracle₁ z.1 ⟨n, by omega⟩ q.1 =
              stageOracle₂ z.1 ⟨n, by omega⟩ q.1 := by
          intro q haction
          have ha := hanswer ⟨n, by omega⟩
          simpa [runnerQuery, state, hs, haction] using ha
        cases haction : policy.rule ⟨n, by omega⟩ (z.2, state.1) with
        | inl output => simp
        | inr query => simp [hq query haction]

/-- In particular, on-run stage-answer coupling preserves the final saved
output of the executable runner. -/
theorem runnerOutput_eq_of_answerAtRunnerQuery
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle₁ stageOracle₂ : Ω → Fin budget → E → Answer)
    (fill : X) (dummy : Answer) (z : Ω × policy.Seed)
    (hanswer : ∀ t : Fin budget,
      stageOracle₁ z.1 t
          (runnerQuery policy stageOracle₁ fill dummy t z).1 =
        stageOracle₂ z.1 t
          (runnerQuery policy stageOracle₁ fill dummy t z).1) :
    runnerOutput policy stageOracle₁ fill dummy z =
      runnerOutput policy stageOracle₂ fill dummy z := by
  have hs := runnerState_eq_of_answerAtRunnerQuery policy
    stageOracle₁ stageOracle₂ fill dummy z hanswer budget le_rfl
  simp only [runnerOutput]
  rw [hs]

section MeasurableRunner

attribute [local instance] BorelStoppingPolicy.seedMeasurable

/-- Joint measurability assumption on a frame-indexed stage oracle.  This is
the precise analytic obligation needed by the executable Borel runner. -/
def JointlyMeasurableStageOracle
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) : Prop :=
  ∀ t : Fin budget,
    Measurable (fun z : Ω × X => stageOracle z.1 t z.2.1)

theorem runnerSnoc_measurable {n : ℕ} :
    Measurable (fun z : OracleHistory X Answer n × (X × Answer) =>
      runnerSnoc z.1 z.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [runnerSnoc] using
      (measurable_snd : Measurable
        (fun z : OracleHistory X Answer n × (X × Answer) => z.2))
  · have hj : Measurable
        (fun z : OracleHistory X Answer n × (X × Answer) => z.1 j) := by
      fun_prop
    simpa only [runnerSnoc_castSucc] using hj

/-- A single runner transition preserves joint measurability. -/
theorem runnerStep_measurable
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (horacle : JointlyMeasurableStageOracle policy stageOracle)
    (t : ℕ) (ht : t < budget)
    (state : Ω × policy.Seed → RunnerState X Answer t)
    (hstate : Measurable state) :
    Measurable (fun z =>
      runnerStep policy stageOracle fill dummy t ht z (state z)) := by
  have horacle_t := horacle ⟨t, ht⟩
  let action := fun z : Ω × policy.Seed =>
    policy.rule ⟨t, Nat.lt_succ_of_lt ht⟩ (z.2, (state z).1)
  have haction : Measurable action := by
    apply (policy.rule_measurable _).comp
    fun_prop
  have hdummy : Measurable (fun _ : Ω × policy.Seed => dummy) := measurable_const
  have hstopSnoc : Measurable (fun z : Ω × policy.Seed =>
      runnerSnoc (state z).1 (fill, dummy)) := by
    have harg : Measurable (fun z : Ω × policy.Seed =>
        ((state z).1, (fill, dummy))) := by
      exact (measurable_fst.comp hstate).prodMk
        ((measurable_const : Measurable
          (fun _ : Ω × policy.Seed => fill)).prodMk hdummy)
    convert runnerSnoc_measurable.comp harg using 1 <;> rfl
  have hstopped : Measurable (fun z : Ω × policy.Seed =>
      (runnerSnoc (state z).1 (fill, dummy),
        (state z).2)) := by
    fun_prop
  have hleft : Measurable
      (fun w : (Ω × policy.Seed) × X =>
        (runnerSnoc (state w.1).1
          (fill, dummy), true, t, w.2)) := by
    have hs : Measurable (fun w : (Ω × policy.Seed) × X =>
        runnerSnoc (state w.1).1
          (fill, dummy)) := by
      have harg : Measurable (fun w : (Ω × policy.Seed) × X =>
          ((state w.1).1,
            (fill, dummy))) := by
        exact ((measurable_fst.comp hstate).comp measurable_fst).prodMk
          ((measurable_const : Measurable
            (fun _ : (Ω × policy.Seed) × X => fill)).prodMk
              (measurable_const : Measurable
                (fun _ : (Ω × policy.Seed) × X => dummy)))
      convert runnerSnoc_measurable.comp harg using 1 <;> rfl
    fun_prop
  have hright : Measurable
      (fun w : (Ω × policy.Seed) × X =>
        (runnerSnoc (state w.1).1
          (w.2, stageOracle w.1.1 ⟨t, ht⟩ w.2.1), false, 0, fill)) := by
    have hanswer : Measurable (fun w : (Ω × policy.Seed) × X =>
        stageOracle w.1.1 ⟨t, ht⟩ w.2.1) := by
      have harg : Measurable (fun w : (Ω × policy.Seed) × X =>
          (w.1.1, w.2)) := by fun_prop
      convert horacle_t.comp harg using 1 <;> rfl
    have hs : Measurable (fun w : (Ω × policy.Seed) × X =>
        runnerSnoc (state w.1).1
          (w.2, stageOracle w.1.1 ⟨t, ht⟩ w.2.1)) := by
      have harg : Measurable (fun w : (Ω × policy.Seed) × X =>
          ((state w.1).1,
            (w.2, stageOracle w.1.1 ⟨t, ht⟩ w.2.1))) := by
        exact ((measurable_fst.comp hstate).comp measurable_fst).prodMk
          (measurable_snd.prodMk hanswer)
      convert runnerSnoc_measurable.comp harg using 1 <;> rfl
    fun_prop
  have hactiveMap : Measurable
      (Sum.elim
        (fun w : (Ω × policy.Seed) × X =>
          (runnerSnoc (state w.1).1
            (fill, dummy), true, t, w.2))
        (fun w : (Ω × policy.Seed) × X =>
          (runnerSnoc (state w.1).1
            (w.2, stageOracle w.1.1 ⟨t, ht⟩ w.2.1), false, 0, fill))) :=
    measurable_fun_sum hleft hright
  have hsplit : Measurable (fun z : Ω × policy.Seed =>
      (MeasurableEquiv.prodSumDistrib (Ω × policy.Seed) X X)
        (z, action z)) :=
    (MeasurableEquiv.prodSumDistrib (Ω × policy.Seed) X X).measurable.comp
      (measurable_id.prodMk haction)
  have hactive := hactiveMap.comp hsplit
  have hflag : Measurable (fun z : Ω × policy.Seed => (state z).2.1) := by
    fun_prop
  have hset : MeasurableSet {z : Ω × policy.Seed | (state z).2.1 = true} :=
    hflag (measurableSet_singleton true)
  have hresult : Measurable (fun z : Ω × policy.Seed =>
      if (state z).2.1 = true then
        (runnerSnoc (state z).1
          (fill, dummy), (state z).2)
      else
        Sum.elim
          (fun w : (Ω × policy.Seed) × X =>
            (runnerSnoc (state w.1).1
              (fill, dummy), true, t, w.2))
          (fun w : (Ω × policy.Seed) × X =>
            (runnerSnoc (state w.1).1
              (w.2, stageOracle w.1.1 ⟨t, ht⟩ w.2.1), false, 0, fill))
          ((MeasurableEquiv.prodSumDistrib (Ω × policy.Seed) X X)
            (z, action z))) :=
    Measurable.ite hset hstopped hactive
  convert hresult using 1
  funext z
  by_cases hs : (state z).2.1 = true
  · simp [runnerStep, hs]
  · simp only [runnerStep, hs, ↓reduceIte]
    cases ha : action z with
    | inl output =>
        simp only [action] at ha
        simp [ha]
        change _ = Sum.elim _ _ (Sum.inl (z, output))
        rfl
    | inr query =>
        simp only [action] at ha
        simp [ha]
        change _ = Sum.elim _ _ (Sum.inr (z, query))
        rfl

/-- Joint measurability of the complete recursive state follows from joint
measurability of the stage oracle; it is not an extra policy assumption. -/
theorem runnerState_measurable_of_stageOracle
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (horacle : JointlyMeasurableStageOracle policy stageOracle)
    (n : ℕ) (hn : n ≤ budget) :
    Measurable (runnerState policy stageOracle fill dummy n hn) := by
  induction n with
  | zero =>
      simp only [runnerState]
      fun_prop
  | succ n ih =>
      have hstep := runnerStep_measurable policy stageOracle fill dummy horacle n
        (by omega)
        (runnerState policy stageOracle fill dummy n (by omega))
        (ih (by omega))
      simpa only [runnerState] using hstep

/-- Joint-measurability certificate for the executable runner.  The state
field is the induction target; query, history, stopped-count and output
measurability are consequences rather than additional assumptions. -/
structure JointlyMeasurableRunner
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer) : Prop where
  stageOracle_joint : JointlyMeasurableStageOracle policy stageOracle
  state_joint : ∀ n (hn : n ≤ budget),
    Measurable (runnerState policy stageOracle fill dummy n hn)

/-- Canonical joint-measurability certificate generated from the sole
analytic input: joint measurability of every stage oracle. -/
theorem jointlyMeasurableRunner_of_stageOracle
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (horacle : JointlyMeasurableStageOracle policy stageOracle) :
    JointlyMeasurableRunner policy stageOracle fill dummy := by
  refine ⟨horacle, ?_⟩
  exact runnerState_measurable_of_stageOracle policy stageOracle fill dummy horacle

theorem JointlyMeasurableRunner.history_joint
    {policy : BorelStoppingPolicy (Answer := Answer) X budget}
    {stageOracle : Ω → Fin budget → E → Answer} {fill : X} {dummy : Answer}
    (h : JointlyMeasurableRunner policy stageOracle fill dummy) :
    Measurable (runnerHistory policy stageOracle fill dummy) := by
  exact measurable_fst.comp (h.state_joint budget le_rfl)

theorem JointlyMeasurableRunner.stoppedAt_joint
    {policy : BorelStoppingPolicy (Answer := Answer) X budget}
    {stageOracle : Ω → Fin budget → E → Answer} {fill : X} {dummy : Answer}
    (h : JointlyMeasurableRunner policy stageOracle fill dummy) :
    Measurable (runnerStoppedAt policy stageOracle fill dummy) := by
  have hs := h.state_joint budget le_rfl
  have hflag : Measurable (fun z =>
      (runnerState policy stageOracle fill dummy budget le_rfl z).2.1) := by
    fun_prop
  have hset : MeasurableSet {z : Ω × policy.Seed |
      (runnerState policy stageOracle fill dummy budget le_rfl z).2.1 = true} :=
    hflag (measurableSet_singleton true)
  exact Measurable.ite hset (by fun_prop) measurable_const

theorem JointlyMeasurableRunner.query_joint
    {policy : BorelStoppingPolicy (Answer := Answer) X budget}
    {stageOracle : Ω → Fin budget → E → Answer} {fill : X} {dummy : Answer}
    (h : JointlyMeasurableRunner policy stageOracle fill dummy) (t : Fin budget) :
    Measurable (runnerQuery policy stageOracle fill dummy t) := by
  let state := fun z : Ω × policy.Seed =>
    runnerState policy stageOracle fill dummy t.1 (Nat.le_of_lt t.2) z
  have hstate : Measurable state := h.state_joint t.1 (Nat.le_of_lt t.2)
  have hflag : Measurable (fun z => (state z).2.1) := by fun_prop
  have hset : MeasurableSet {z : Ω × policy.Seed | (state z).2.1 = true} :=
    hflag (measurableSet_singleton true)
  have hinput : Measurable (fun z : Ω × policy.Seed => (z.2, (state z).1)) := by
    fun_prop
  have haction := (policy.rule_measurable
    ⟨t.1, Nat.lt_succ_of_lt t.2⟩).comp hinput
  have hpick : Measurable
      (Sum.elim (fun _ : X => fill) id : OracleAction X → X) :=
    measurable_fun_sum measurable_const measurable_id
  have hresult : Measurable (fun z => if (state z).2.1 then fill else
      Sum.elim (fun _ : X => fill) id
        (policy.rule ⟨t.1, Nat.lt_succ_of_lt t.2⟩ (z.2, (state z).1))) :=
    Measurable.ite hset measurable_const (hpick.comp haction)
  convert hresult using 1
  funext z
  by_cases hb : (state z).2.1 = true
  · simp [runnerQuery, state, hb]
  · simp only [runnerQuery, state, hb, ↓reduceIte]
    cases policy.rule ⟨t.1, Nat.lt_succ_of_lt t.2⟩
        (z.2, (state z).1) <;> rfl

theorem JointlyMeasurableRunner.output_joint
    {policy : BorelStoppingPolicy (Answer := Answer) X budget}
    {stageOracle : Ω → Fin budget → E → Answer} {fill : X} {dummy : Answer}
    (h : JointlyMeasurableRunner policy stageOracle fill dummy) :
    Measurable (runnerOutput policy stageOracle fill dummy) := by
  let state := fun z : Ω × policy.Seed =>
    runnerState policy stageOracle fill dummy budget le_rfl z
  have hstate : Measurable state := h.state_joint budget le_rfl
  have hflag : Measurable (fun z => (state z).2.1) := by fun_prop
  have hset : MeasurableSet {z : Ω × policy.Seed | (state z).2.1 = true} :=
    hflag (measurableSet_singleton true)
  have hinput : Measurable (fun z : Ω × policy.Seed => (z.2, (state z).1)) := by
    fun_prop
  have haction := (policy.rule_measurable
    ⟨budget, Nat.lt_succ_self budget⟩).comp hinput
  have hpick : Measurable
      (Sum.elim id (fun _ : X => fill) : OracleAction X → X) :=
    measurable_fun_sum measurable_id measurable_const
  have hresult : Measurable (fun z => if (state z).2.1 then (state z).2.2.2 else
      Sum.elim id (fun _ : X => fill)
        (policy.rule ⟨budget, Nat.lt_succ_self budget⟩ (z.2, (state z).1))) :=
    Measurable.ite hset (by fun_prop) (hpick.comp haction)
  convert hresult using 1
  funext z
  by_cases hb : (state z).2.1 = true
  · simp [runnerOutput, state, hb]
  · simp only [runnerOutput, state, hb, ↓reduceIte]
    cases policy.rule ⟨budget, Nat.lt_succ_self budget⟩
        (z.2, (state z).1) <;> rfl

end MeasurableRunner

section PrefixDependence

/-- Stage `t` of an online oracle may inspect exactly the first `t+1` frame
columns.  Consequently the state before stage `t`, and hence the query chosen
at that stage, depends on only the first `t` columns. -/
def StageOracleDependsOnFramePrefix {m : ℕ}
    (frame : Ω → Fin m → E)
    (stageOracle : Ω → Fin budget → E → Answer) : Prop :=
  ∀ (t : Fin budget) (omega omega' : Ω),
    (∀ j : Fin m, j.1 < t.1 + 1 → frame omega j = frame omega' j) →
    ∀ x : E, stageOracle omega t x = stageOracle omega' t x

/-- The full operational state after `n` stages depends only on the first
`n` frame columns. -/
theorem runnerState_eq_of_framePrefix {m : ℕ}
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (frame : Ω → Fin m → E)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (horacle : StageOracleDependsOnFramePrefix frame stageOracle)
    (n : ℕ) (hn : n ≤ budget) (omega omega' : Ω) (seed : policy.Seed)
    (hprefix : ∀ j : Fin m, j.1 < n → frame omega j = frame omega' j) :
    runnerState policy stageOracle fill dummy n hn (omega, seed) =
      runnerState policy stageOracle fill dummy n hn (omega', seed) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprev := ih (by omega) (fun j hj => hprefix j (by omega))
      rw [runnerState, runnerState, hprev]
      have hstage : ∀ x : E,
          stageOracle omega ⟨n, by omega⟩ x =
            stageOracle omega' ⟨n, by omega⟩ x := by
        intro x
        apply horacle ⟨n, by omega⟩ omega omega'
        intro j hj
        exact hprefix j (by omega)
      simp only [runnerStep]
      let state := runnerState policy stageOracle fill dummy n (by omega) (omega', seed)
      by_cases hs : state.2.1
      · simp [state, hs, hstage]
      · simp only [state, hs, ↓reduceIte]
        cases haction : policy.rule ⟨n, by omega⟩ (seed, state.1) <;>
          simp [haction, hstage]

/-- The exposed query at stage `t` is online: for a fixed policy seed it
depends only on the `t` already available frame columns. -/
theorem runnerQuery_dependsOnlyOnFramePrefix {m : ℕ}
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (frame : Ω → Fin m → E)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (horacle : StageOracleDependsOnFramePrefix frame stageOracle)
    (seed : policy.Seed) (t : Fin budget) :
    DependsOnlyOnFramePrefix frame t.1
      (fun omega => (runnerQuery policy stageOracle fill dummy t (omega, seed)).1) := by
  intro omega omega' hprefix
  have hstate := runnerState_eq_of_framePrefix policy frame stageOracle fill dummy
    horacle t.1 (Nat.le_of_lt t.2) omega omega' seed hprefix
  simp only [runnerQuery]
  rw [hstate]

/-- The final saved output depends only on the whole revealed frame prefix. -/
theorem runnerOutput_dependsOnlyOnFramePrefix {m : ℕ}
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (frame : Ω → Fin m → E)
    (stageOracle : Ω → Fin budget → E → Answer) (fill : X) (dummy : Answer)
    (horacle : StageOracleDependsOnFramePrefix frame stageOracle)
    (seed : policy.Seed) :
    DependsOnlyOnFramePrefix frame budget
      (fun omega => (runnerOutput policy stageOracle fill dummy (omega, seed)).1) := by
  intro omega omega' hprefix
  have hstate := runnerState_eq_of_framePrefix policy frame stageOracle fill dummy
    horacle budget le_rfl omega omega' seed hprefix
  simp only [runnerOutput]
  rw [hstate]

end PrefixDependence

end Runner

end BorelStoppingPolicy

end VIReference.Pilot
