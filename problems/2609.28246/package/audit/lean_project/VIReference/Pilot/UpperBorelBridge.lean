import VIReference.Pilot.ModelMeasurableSelector
import VIReference.Pilot.AdmissibleOracle

/-!
# Borel execution bridge for capped upper programs

`ExactJetProgram` deliberately permits arbitrary continuations.  Consequently
there is no sound compiler from every value of that type to a Borel policy.
This module isolates the missing, auditable datum: measurability of the action
obtained by replaying the program on every fixed-length transcript.  A capped
program carrying that datum compiles to the source-facing early-stopping
policy, with a singleton seed and no operational padding.
-/

open Set MeasureTheory

namespace VIReference.Pilot

noncomputable section

universe u v w uo

/-- The disjoint-union measurable structure on an optional value.  Mathlib
does not install this instance globally, while program outcomes use `Option`
essentially. -/
noncomputable instance upperOptionMeasurableSpace {A : Type uo}
    [MeasurableSpace A] : MeasurableSpace (Option A) :=
  (inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit.{0, uo} A)

theorem measurable_optionEquivSumPUnit {A : Type uo} [MeasurableSpace A] :
    Measurable (Equiv.optionEquivSumPUnit.{0, uo} A) := by
  apply Measurable.of_comap_le
  rfl

theorem measurable_optionEquivSumPUnit_symm {A : Type uo} [MeasurableSpace A] :
    Measurable (Equiv.optionEquivSumPUnit.{0, uo} A).symm := by
  apply Measurable.of_comap_le
  rw [show upperOptionMeasurableSpace =
      (inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
        (Equiv.optionEquivSumPUnit.{0, uo} A) from rfl]
  rw [MeasurableSpace.comap_comp]
  simpa

theorem measurable_some {A : Type uo} [MeasurableSpace A] :
    Measurable (Option.some : A → Option A) := by
  have hm := measurable_optionEquivSumPUnit_symm.comp
    (@measurable_inl A PUnit _ _)
  convert hm using 1
  funext x
  rfl

protected theorem Measurable.some {S : Type*} {A : Type uo}
    [MeasurableSpace S] [MeasurableSpace A] {f : S → A}
    (hf : Measurable f) : Measurable (fun x => some (f x)) :=
  measurable_some.comp hf

theorem measurable_option_elim {A : Type uo} {B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (fallback : B)
    (someCase : A → B) (hsome : Measurable someCase) :
    Measurable (fun value : Option A => value.elim fallback someCase) := by
  have hm : Measurable
      (Sum.elim someCase (fun _ : PUnit => fallback) ∘
        Equiv.optionEquivSumPUnit.{0, uo} A) :=
    (hsome.sumElim measurable_const).comp measurable_optionEquivSumPUnit
  convert hm using 1
  funext value
  cases value <;> rfl

namespace ExactJetProgram

variable {X Answer Output : Type*}

/-- Replay a list of oracle answers and return the residual program. -/
def residualAfterAnswers : ExactJetProgram X Answer Output →
    List Answer → ExactJetProgram X Answer Output
  | program, [] => program
  | .halt result, _ :: _ => .halt result
  | .query _ next, answer :: answers =>
      residualAfterAnswers (next answer) answers

/-- Replay the answers in a fixed-length transcript.  Transcript query points
are deliberately ignored: on a genuine run they are checked separately by
`BorelStoppingPolicy.IsUnpaddedRun`. -/
def residualAfterHistory (program : ExactJetProgram X Answer Output)
    {n : ℕ} (history : Fin n → X × Answer) : ExactJetProgram X Answer Output :=
  residualAfterAnswers program (List.ofFn (fun i => (history i).2))

@[simp] theorem residualAfterAnswers_halt
    (result : Option Output) (answers : List Answer) :
    residualAfterAnswers (.halt result : ExactJetProgram X Answer Output) answers =
      .halt result := by
  cases answers <;> rfl

/-- The source-facing stop/query action exposed after replaying a transcript.
`finish` maps both successful and explicitly failed program results to a total
feasible output; for certified calls, failure is sent to the public fallback. -/
def replayAction (finish : Option Output → X)
    (program : ExactJetProgram X Answer Output) {n : ℕ}
    (history : Fin n → X × Answer) : Sum X X :=
  match residualAfterHistory program history with
  | .halt result => Sum.inl (finish result)
  | .query point _ => Sum.inr point

@[simp] theorem residualAfterHistory_zero
    (program : ExactJetProgram X Answer Output)
    (history : Fin 0 → X × Answer) :
    residualAfterHistory program history = program := by
  simp [residualAfterHistory, residualAfterAnswers]

@[simp] theorem residualAfterHistory_halt
    (result : Option Output) {n : ℕ} (history : Fin n → X × Answer) :
    residualAfterHistory (.halt result : ExactJetProgram X Answer Output) history =
      .halt result := by
  simp [residualAfterHistory]

theorem residualAfterAnswers_locallyCapped
    (program : ExactJetProgram X Answer Output) (cap : ℕ)
    (answers : List Answer) (hlength : answers.length = cap) :
    ∃ result,
      residualAfterAnswers (program.locallyCapped cap) answers = .halt result := by
  induction cap generalizing program answers with
  | zero =>
      cases answers with
      | nil =>
          cases program <;>
            simp [ExactJetProgram.locallyCapped, residualAfterAnswers]
      | cons answer answers => simp at hlength
  | succ cap ih =>
      cases answers with
      | nil => simp at hlength
      | cons answer answers =>
          have htail : answers.length = cap := by simpa using hlength
          cases program with
          | halt result =>
              exact ⟨result, by simp [ExactJetProgram.locallyCapped,
                residualAfterAnswers]⟩
          | query point next =>
              simpa [ExactJetProgram.locallyCapped, residualAfterAnswers] using
                ih (next answer) answers htail

/-- Installing a cap before replay guarantees that the cap-length rule is a
stop on every transcript, including counterfactual ones. -/
theorem residualAfterHistory_locallyCapped_cap
    (program : ExactJetProgram X Answer Output) (cap : ℕ)
    (history : Fin cap → X × Answer) :
    ∃ result, residualAfterHistory (program.locallyCapped cap) history = .halt result := by
  apply residualAfterAnswers_locallyCapped program cap
  simp

/-- Restrict a generic finite transcript to a prefix. -/
def restrictTranscript {A : Type*} {m n : ℕ} (history : Fin m → A)
    (hn : n ≤ m) : Fin n → A :=
  fun i => history ⟨i.1, lt_of_lt_of_le i.2 hn⟩

@[simp] theorem restrictTranscript_eq_oracleHistory_restrict
    {E₀ Answer₀ : Type*} {X₀ : Set E₀} {m n : ℕ}
    (history : OracleHistory X₀ Answer₀ m) (hn : n ≤ m) :
    restrictTranscript history hn = OracleHistory.restrict history hn := rfl

/-- Replay-level formulation of a genuine run, before attaching a cap. -/
def IsReplayedRun (finish : Option Output → X)
    (program : ExactJetProgram X Answer Output) (oracle : X → Answer)
  (n : ℕ) (history : Fin n → X × Answer) (output : X) : Prop :=
  (∀ i : Fin n,
    replayAction finish program
        (restrictTranscript history (Nat.le_of_lt i.2)) =
      Sum.inr (history i).1 ∧
    (history i).2 = oracle (history i).1) ∧
  replayAction finish program history = Sum.inl output

/-- Prepending one query/answer pair commutes with replay. -/
theorem replayAction_cons_query (finish : Option Output → X)
    (point : X) (next : Answer → ExactJetProgram X Answer Output)
    (answer : Answer) {n : ℕ} (history : Fin n → X × Answer) :
    replayAction finish (.query point next)
        (Fin.cons (point, answer) history) =
      replayAction finish (next answer) history := by
  simp [replayAction, residualAfterHistory, List.ofFn_cons,
    residualAfterAnswers]

/-- Every big-step execution has a genuine replay transcript with exactly the
same number of queries and the same projected output. -/
theorem Evaluates.exists_isReplayedRun {oracle : X → Answer}
    (finish : Option Output → X)
    {program : ExactJetProgram X Answer Output} {used : ℕ}
    {result : Option Output} (heval : Evaluates oracle program used result) :
    ∃ history : Fin used → X × Answer,
      IsReplayedRun finish program oracle used history (finish result) := by
  induction heval with
  | halt result =>
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      simp [IsReplayedRun, replayAction]
  | query point next used result hnext ih =>
      obtain ⟨tail, htail, htailStop⟩ := ih
      let history : Fin (used + 1) → X × Answer :=
        Fin.cons (point, oracle point) tail
      refine ⟨history, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · constructor
          · simp [history, replayAction, restrictTranscript,
              residualAfterHistory, residualAfterAnswers]
          · rfl
        · constructor
          · let prefixHistory : Fin (j.1 + 1) → X × Answer :=
                restrictTranscript history
                  (Nat.succ_le_succ (Nat.le_of_lt j.2))
            have hrestrict : prefixHistory =
                  Fin.cons (point, oracle point)
                    (restrictTranscript tail (Nat.le_of_lt j.2)) := by
                funext k
                refine Fin.cases ?_ (fun l => ?_) k
                · simp [prefixHistory, history, restrictTranscript]
                · let l' : Fin used :=
                    ⟨l.1, lt_trans l.2 j.2⟩
                  calc
                    prefixHistory l.succ = history l'.succ := by
                      apply congrArg history
                      apply Fin.ext
                      rfl
                    _ = tail l' := by simp [history]
                    _ = restrictTranscript tail (Nat.le_of_lt j.2) l := by
                      apply congrArg tail
                      apply Fin.ext
                      rfl
                    _ = (Fin.cons (α := fun _ => X × Answer)
                        (point, oracle point)
                        (restrictTranscript tail (Nat.le_of_lt j.2))) l.succ := by
                      symm
                      exact Fin.cons_succ (α := fun _ => X × Answer)
                        (point, oracle point)
                        (restrictTranscript tail (Nat.le_of_lt j.2)) l
            have hj := (htail j).1
            change replayAction finish (.query point next)
              prefixHistory =
                Sum.inr (tail j).1
            rw [hrestrict]
            exact (replayAction_cons_query finish point next (oracle point)
              (restrictTranscript tail (Nat.le_of_lt j.2))).trans hj
          · simpa [history] using (htail j).2
      · simpa [history] using
          (replayAction_cons_query finish point next (oracle point) tail).trans
            htailStop

section MeasurableAction

variable [MeasurableSpace X] [MeasurableSpace Answer]

/-- Borel replayability of one program for every fixed transcript length. -/
def IsBorelAction (finish : Option Output → X)
    (program : ExactJetProgram X Answer Output) : Prop :=
  ∀ n, Measurable (fun history : Fin n → X × Answer =>
    replayAction finish program history)

/-- Joint version used to audit finite recursions whose public/internal state
varies measurably. -/
def IsJointlyBorelAction {P : Type*} [MeasurableSpace P]
    (finish : Option Output → X)
    (program : P → ExactJetProgram X Answer Output) : Prop :=
  ∀ n, Measurable (fun z : P × (Fin n → X × Answer) =>
    replayAction finish (program z.1) z.2)

theorem IsJointlyBorelAction.fixed {P : Type*} [MeasurableSpace P]
    {finish : Option Output → X}
    {program : P → ExactJetProgram X Answer Output}
    (h : IsJointlyBorelAction finish program) (parameter : P) :
    IsBorelAction finish (program parameter) := by
  intro n
  exact (h n).comp (measurable_const.prodMk measurable_id)

theorem isJointlyBorelAction_halt {P : Type*} [MeasurableSpace P]
    (finish : Option Output → X) (result : P → Option Output)
    (hresult : Measurable (fun p => finish (result p))) :
    IsJointlyBorelAction finish
      (fun p => (.halt (result p) : ExactJetProgram X Answer Output)) := by
  intro n
  have hm := (@measurable_inl X X _ _).comp
    (hresult.comp (measurable_fst : Measurable (Prod.fst :
      P × (Fin n → X × Answer) → P)))
  convert hm using 1
  funext z
  simp [replayAction]

theorem replayAction_query_succ (finish : Option Output → X)
    (point : X) (next : Answer → ExactJetProgram X Answer Output)
    {n : ℕ} (history : Fin (n + 1) → X × Answer) :
    replayAction finish (.query point next) history =
      replayAction finish (next (history 0).2) (fun i => history i.succ) := by
  simp [replayAction, residualAfterHistory, List.ofFn_succ,
    residualAfterAnswers]

theorem isJointlyBorelAction_query {P : Type*} [MeasurableSpace P]
    (finish : Option Output → X) (point : P → X)
    (next : P × Answer → ExactJetProgram X Answer Output)
    (hpoint : Measurable point)
    (hnext : IsJointlyBorelAction finish next) :
    IsJointlyBorelAction finish
      (fun p => .query (point p) (fun answer => next (p, answer))) := by
  intro n
  cases n with
  | zero =>
      convert measurable_inr.comp (hpoint.comp measurable_fst) using 1 <;>
        rfl
  | succ n =>
      have harg : Measurable (fun z :
          P × (Fin (n + 1) → X × Answer) =>
          ((z.1, (z.2 0).2), fun i : Fin n => z.2 i.succ)) := by
        fun_prop
      have hcomp := (hnext n).comp harg
      convert hcomp using 1
      funext z
      exact replayAction_query_succ finish (point z.1)
        (fun answer => next (z.1, answer)) z.2

noncomputable def actionPiecewise {P : Type*} (s : Set P)
    (first second : P → ExactJetProgram X Answer Output) (p : P) :
    ExactJetProgram X Answer Output := by
  classical
  exact if p ∈ s then first p else second p

theorem isJointlyBorelAction_piecewise {P : Type*} [MeasurableSpace P]
    (finish : Option Output → X) (s : Set P) (hs : MeasurableSet s)
    (first second : P → ExactJetProgram X Answer Output)
    (hfirst : IsJointlyBorelAction finish first)
    (hsecond : IsJointlyBorelAction finish second) :
    IsJointlyBorelAction finish
      (actionPiecewise s first second) := by
  classical
  intro n
  have hset : MeasurableSet
      {z : P × (Fin n → X × Answer) | z.1 ∈ s} :=
    hs.preimage measurable_fst
  letI : DecidablePred (fun z : P × (Fin n → X × Answer) =>
      z.1 ∈ s) := Classical.decPred _
  have hite : Measurable (fun z : P × (Fin n → X × Answer) =>
      if z.1 ∈ s then replayAction finish (first z.1) z.2
      else replayAction finish (second z.1) z.2) :=
    Measurable.ite hset (hfirst n) (hsecond n)
  convert hite using 1
  funext z
  by_cases hz : z.1 ∈ s <;> simp [actionPiecewise, hz]

end MeasurableAction

section MeasurableOutcome

variable [MeasurableSpace X] [MeasurableSpace Answer]

/-- Replay observation that retains a terminal program value.  This stronger
observable is useful for compositional proofs: later public query points may
depend measurably on an earlier subprogram's returned value. -/
def replayOutcomeAction (program : ExactJetProgram X Answer Output)
    {n : ℕ} (history : Fin n → X × Answer) : Sum (Option Output) X :=
  match residualAfterHistory program history with
  | .halt result => Sum.inl result
  | .query point _ => Sum.inr point

/-- Every fixed-length replay observation of a program is measurable. -/
def IsBorelOutcome [MeasurableSpace Output]
    (program : ExactJetProgram X Answer Output) : Prop :=
  ∀ n, Measurable (fun history : Fin n → X × Answer =>
    replayOutcomeAction program history)

/-- Joint outcome measurability for a measurably varying public state. -/
def IsJointlyBorelOutcome {P : Type*} [MeasurableSpace P]
    [MeasurableSpace Output]
    (program : P → ExactJetProgram X Answer Output) : Prop :=
  ∀ n, Measurable (fun z : P × (Fin n → X × Answer) =>
    replayOutcomeAction (program z.1) z.2)

theorem IsJointlyBorelOutcome.fixed {P : Type*} [MeasurableSpace P]
    [MeasurableSpace Output]
    {program : P → ExactJetProgram X Answer Output}
    (h : IsJointlyBorelOutcome program) (parameter : P) :
    IsBorelOutcome (program parameter) := by
  intro n
  exact (h n).comp (measurable_const.prodMk measurable_id)

theorem IsJointlyBorelOutcome.compParameter
    {P Q : Type*} [MeasurableSpace P] [MeasurableSpace Q]
    [MeasurableSpace Output]
    {program : P → ExactJetProgram X Answer Output}
    (h : IsJointlyBorelOutcome program) (g : Q → P) (hg : Measurable g) :
    IsJointlyBorelOutcome (fun q => program (g q)) := by
  intro n
  exact (h n).comp ((hg.comp measurable_fst).prodMk measurable_snd)

theorem isJointlyBorelOutcome_halt {P : Type*} [MeasurableSpace P]
    [MeasurableSpace Output] (result : P → Option Output)
    (hresult : Measurable result) :
    IsJointlyBorelOutcome
      (fun p => (.halt (result p) : ExactJetProgram X Answer Output)) := by
  intro n
  have hm := (@measurable_inl (Option Output) X _ _).comp
    (hresult.comp (measurable_fst : Measurable (Prod.fst :
      P × (Fin n → X × Answer) → P)))
  convert hm using 1
  funext z
  simp [replayOutcomeAction]

theorem replayOutcomeAction_query_succ
    (point : X) (next : Answer → ExactJetProgram X Answer Output)
    {n : ℕ} (history : Fin (n + 1) → X × Answer) :
    replayOutcomeAction (.query point next) history =
      replayOutcomeAction (next (history 0).2) (fun i => history i.succ) := by
  simp [replayOutcomeAction, residualAfterHistory, List.ofFn_succ,
    residualAfterAnswers]

theorem isJointlyBorelOutcome_query {P : Type*} [MeasurableSpace P]
    [MeasurableSpace Output] (point : P → X)
    (next : P × Answer → ExactJetProgram X Answer Output)
    (hpoint : Measurable point)
    (hnext : IsJointlyBorelOutcome next) :
    IsJointlyBorelOutcome
      (fun p => .query (point p) (fun answer => next (p, answer))) := by
  intro n
  cases n with
  | zero =>
      convert (@measurable_inr (Option Output) X _ _).comp
        (hpoint.comp measurable_fst) using 1 <;> rfl
  | succ n =>
      have harg : Measurable (fun z :
          P × (Fin (n + 1) → X × Answer) =>
          ((z.1, (z.2 0).2), fun i : Fin n => z.2 i.succ)) := by
        fun_prop
      have hcomp := (hnext n).comp harg
      convert hcomp using 1
      funext z
      exact replayOutcomeAction_query_succ (point z.1)
        (fun answer => next (z.1, answer)) z.2

theorem isJointlyBorelOutcome_piecewise {P : Type*} [MeasurableSpace P]
    [MeasurableSpace Output] (s : Set P) (hs : MeasurableSet s)
    (first second : P → ExactJetProgram X Answer Output)
    (hfirst : IsJointlyBorelOutcome first)
    (hsecond : IsJointlyBorelOutcome second) :
    IsJointlyBorelOutcome (actionPiecewise s first second) := by
  classical
  intro n
  have hset : MeasurableSet
      {z : P × (Fin n → X × Answer) | z.1 ∈ s} :=
    hs.preimage measurable_fst
  letI : DecidablePred (fun z : P × (Fin n → X × Answer) =>
      z.1 ∈ s) := Classical.decPred _
  have hite : Measurable (fun z : P × (Fin n → X × Answer) =>
      if z.1 ∈ s then replayOutcomeAction (first z.1) z.2
      else replayOutcomeAction (second z.1) z.2) :=
    Measurable.ite hset (hfirst n) (hsecond n)
  convert hite using 1
  funext z
  by_cases hz : z.1 ∈ s <;> simp [actionPiecewise, hz]

/-- Forgetting the terminal certificate but retaining its total feasible
projection turns outcome measurability into the source action condition. -/
theorem IsBorelOutcome.isBorelAction [MeasurableSpace Output]
    {program : ExactJetProgram X Answer Output} (h : IsBorelOutcome program)
    (finish : Option Output → X) (hfinish : Measurable finish) :
    IsBorelAction finish program := by
  intro n
  have hpost : Measurable (Sum.elim (Sum.inl ∘ finish) Sum.inr :
      Sum (Option Output) X → Sum X X) :=
    (measurable_inl.comp hfinish).sumElim measurable_inr
  have hm := hpost.comp (h n)
  convert hm using 1
  funext history
  simp only [Function.comp_apply]
  unfold replayOutcomeAction replayAction
  split <;> rfl

/-- Replaying through a locally installed cap commutes with replaying the
uncapped program, with exactly the unused fuel left over. -/
theorem residualAfterAnswers_locallyCapped_of_length_le
    (program : ExactJetProgram X Answer Output) (cap : ℕ)
    (answers : List Answer) (hanswers : answers.length ≤ cap) :
    residualAfterAnswers (program.locallyCapped cap) answers =
      (residualAfterAnswers program answers).locallyCapped
        (cap - answers.length) := by
  induction answers generalizing program cap with
  | nil => simp [residualAfterAnswers]
  | cons answer answers ih =>
      cases cap with
      | zero => simp at hanswers
      | succ cap =>
          cases program with
          | halt result =>
              simp [residualAfterAnswers, ExactJetProgram.locallyCapped]
          | query point next =>
              simp only [ExactJetProgram.locallyCapped, residualAfterAnswers,
                List.length_cons, Nat.succ_sub_succ_eq_sub]
              apply ih
              simpa only [List.length_cons, Nat.succ_le_succ_iff] using hanswers

/-- Postprocess a raw terminal outcome with a total feasible output map. -/
def outcomeToAction (finish : Option Output → X) :
    Sum (Option Output) X → Sum X X :=
  Sum.elim (Sum.inl ∘ finish) Sum.inr

/-- At the exact hard cap, a residual query is converted to explicit failure
and hence to the same total fallback as `halt none`. -/
def outcomeToCapAction (finish : Option Output → X) :
    Sum (Option Output) X → Sum X X :=
  Sum.elim (Sum.inl ∘ finish) (fun _ => Sum.inl (finish none))

theorem measurable_outcomeToAction [MeasurableSpace Output]
    (finish : Option Output → X) (hfinish : Measurable finish) :
    Measurable (outcomeToAction finish) :=
  (measurable_inl.comp hfinish).sumElim measurable_inr

theorem measurable_outcomeToCapAction [MeasurableSpace Output]
    (finish : Option Output → X) (hfinish : Measurable finish) :
    Measurable (outcomeToCapAction finish) :=
  (measurable_inl.comp hfinish).sumElim measurable_const

/-- Outcome measurability of the uncapped program is sufficient to audit all
rules of its hard-capped action.  At `n = cap` the rule always stops. -/
theorem IsBorelOutcome.locallyCappedAction [MeasurableSpace Output]
    {program : ExactJetProgram X Answer Output} (h : IsBorelOutcome program)
    (cap : ℕ) (finish : Option Output → X) (hfinish : Measurable finish)
    (n : ℕ) (hn : n ≤ cap) :
    Measurable (fun history : Fin n → X × Answer =>
      replayAction finish (program.locallyCapped cap) history) := by
  by_cases hlt : n < cap
  · have heq : (fun history : Fin n → X × Answer =>
        replayAction finish (program.locallyCapped cap) history) =
      outcomeToAction finish ∘ (fun history =>
        replayOutcomeAction program history) := by
      funext history
      unfold replayAction replayOutcomeAction residualAfterHistory
      rw [residualAfterAnswers_locallyCapped_of_length_le program cap _ (by simpa)]
      cases hres : residualAfterAnswers program
          (List.ofFn fun i => (history i).2) with
      | halt result =>
          simp [hres, ExactJetProgram.locallyCapped, outcomeToAction]
      | query point next =>
          obtain ⟨left, hleft⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt))
          have hlen : (List.ofFn fun i => (history i).2).length = n := by simp
          rw [hlen, hleft]
          simp [hres, ExactJetProgram.locallyCapped, outcomeToAction]
    rw [heq]
    exact (measurable_outcomeToAction finish hfinish).comp (h n)
  · have hncap : n = cap := by omega
    subst n
    have heq : (fun history : Fin cap → X × Answer =>
        replayAction finish (program.locallyCapped cap) history) =
      outcomeToCapAction finish ∘ (fun history =>
        replayOutcomeAction program history) := by
      funext history
      unfold replayAction replayOutcomeAction residualAfterHistory
      rw [residualAfterAnswers_locallyCapped_of_length_le program cap _ (by simp)]
      cases hres : residualAfterAnswers program
          (List.ofFn fun i => (history i).2) <;>
        simp [hres, ExactJetProgram.locallyCapped, outcomeToCapAction]
    rw [heq]
    exact (measurable_outcomeToCapAction finish hfinish).comp (h cap)

end MeasurableOutcome

end ExactJetProgram

section Compiler

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Finite-dimensional continuous multilinear-map spaces are second
countable.  Mathlib does not currently install this recursive instance, so we
record it locally to compare the two jet sigma algebras. -/
@[reducible] noncomputable def cmlmSecondCountableTopology :
    (n : ℕ) → SecondCountableTopology (E [×n]→L[ℝ] E)
  | 0 =>
      (continuousMultilinearCurryFin0 ℝ E E).toHomeomorph.secondCountableTopology
  | n + 1 => by
      letI : SecondCountableTopology (E [×n]→L[ℝ] E) :=
        cmlmSecondCountableTopology n
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) E).toHomeomorph.secondCountableTopology

/-- The componentwise measurable structure already carried by
`SymmetricExactJet` is exactly its norm-Borel structure in the finite
dimensional setting of the theorem.  Thus the compiler and the continuous
selector use the same sigma algebra, rather than silently changing it. -/
theorem symmetricExactJet_measurable_eq_normBorel (p : ℕ) :
    (inferInstance : MeasurableSpace (SymmetricExactJet E p)) =
      upperJetBorelMeasurableSpace p := by
  letI (n : ℕ) : SecondCountableTopology (E [×n]→L[ℝ] E) :=
    cmlmSecondCountableTopology n
  exact BorelSpace.measurable_eq

/-- The feasible subtype measurable structure is likewise the norm-Borel
subtype structure named by the upper selector module. -/
theorem feasible_measurable_eq_normBorel (data : VIPublicData E) :
    (inferInstance : MeasurableSpace data.X) =
      upperFeasibleBorelMeasurableSpace data := by
  simpa [upperFeasibleBorelMeasurableSpace] using congrArg
    (fun m : MeasurableSpace E =>
      @Subtype.instMeasurableSpace E (fun x => x ∈ data.X) m)
    (show (inferInstance : MeasurableSpace E) = borel E from
      BorelSpace.measurable_eq)

/-- Total output projection for a certified call.  A genuine certificate
returns its own feasible point; explicit failure stops at the public fallback. -/
def certifiedCallOutput (data : VIPublicData E) (fallback : data.X) :
    Option (EvaluatedNormalCertificate data) → data.X
  | some cert => cert.point
  | none => fallback

/-- A total ambient answer function used only by the generic execution
semantics.  On every feasible query it is exactly the supplied feasible
oracle; its arbitrary off-domain branch is never queried by a policy. -/
noncomputable def FeasibleExactSymmetricJetOracle.totalAnswer
    (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F) (fallback : data.X) :
    E → SymmetricExactJet E data.p := by
  classical
  exact fun x =>
    if hx : x ∈ data.X then oracle.answer ⟨x, hx⟩ else oracle.answer fallback

@[simp] theorem FeasibleExactSymmetricJetOracle.totalAnswer_coe
    (data : VIPublicData E) (F : E → E)
    (oracle : FeasibleExactSymmetricJetOracle data F) (fallback point : data.X) :
    oracle.totalAnswer data F fallback point.1 = oracle.answer point := by
  classical
  simp [FeasibleExactSymmetricJetOracle.totalAnswer, point.2]

/-- Success semantics using exactly the feasible oracle furnished by the
admissible class.  The ambient totalization is semantically inert because
every policy query has subtype `data.X`. -/
def BorelStoppingPolicy.RunSucceedsOnFeasible (data : VIPublicData E)
    (F : E → E) (epsilon : ℝ)
    (policy : BorelStoppingPolicy (Answer := SymmetricExactJet E data.p)
      data.X budget)
    (oracle : FeasibleExactSymmetricJetOracle data F) (fallback : data.X)
    (seed : policy.Seed) (n : ℕ) (hn : n ≤ budget)
    (history : OracleHistory data.X (SymmetricExactJet E data.p) n)
    (output : data.X) : Prop :=
  policy.IsUnpaddedRun (oracle.totalAnswer data F fallback) seed n hn history output ∧
    tangentResidual data F output.1 ≤ epsilon

/-- The exact extra condition absent from `ExactJetProgram`: every action
obtained on every transcript length up to the installed cap is measurable.
This condition mentions no unknown operator and no success certificate. -/
def CappedExactJetCall.IsBorel (data : VIPublicData E)
    (call : CappedExactJetCall data) (fallback : data.X) : Prop :=
  ∀ n : Fin (call.cap + 1), Measurable (fun history :
      OracleHistory data.X (SymmetricExactJet E data.p) n.1 =>
    ExactJetProgram.replayAction (certifiedCallOutput data fallback)
      (call.program.locallyCapped call.cap) history)

/-- A stronger measurable terminal-outcome proof discharges the exact Borel
condition of a capped call. -/
theorem CappedExactJetCall.isBorel_of_isBorelOutcome
    (data : VIPublicData E) (call : CappedExactJetCall data)
    (fallback : data.X)
    [MeasurableSpace (EvaluatedNormalCertificate data)]
    (hprogram : call.program.IsBorelOutcome)
    (hfinish : Measurable (certifiedCallOutput data fallback)) :
    call.IsBorel data fallback := by
  intro n
  exact hprogram.locallyCappedAction call.cap
    (certifiedCallOutput data fallback) hfinish n.1
    (Nat.le_of_lt_succ n.2)

/-- A capped upper call together with the Borel datum needed by the frozen
`def:policy` contract. -/
structure BorelCappedExactJetCall (data : VIPublicData E) where
  call : CappedExactJetCall data
  fallback : data.X
  action_measurable : call.IsBorel data fallback

/-- Compile a measurably replayable capped call to a deterministic Borel
early-stopping policy.  The cap is installed in the replayed program itself. -/
def BorelCappedExactJetCall.toPolicy (data : VIPublicData E)
    (bcall : BorelCappedExactJetCall data) :
    BorelStoppingPolicy (Answer := SymmetricExactJet E data.p)
      data.X bcall.call.cap where
  Seed := PUnit
  seedMeasurable := ⊤
  seedMeasure := Measure.dirac PUnit.unit
  seedProbability := by infer_instance
  rule n state :=
    ExactJetProgram.replayAction (certifiedCallOutput data bcall.fallback)
      (bcall.call.program.locallyCapped bcall.call.cap) state.2
  rule_measurable n := by
    exact (bcall.action_measurable n).comp measurable_snd
  cap_stops state := by
    obtain ⟨result, hresult⟩ :=
      ExactJetProgram.residualAfterHistory_locallyCapped_cap
        bcall.call.program bcall.call.cap state.2
    refine ⟨certifiedCallOutput data bcall.fallback result, ?_⟩
    simp [ExactJetProgram.replayAction, hresult]

theorem BorelCappedExactJetCall.toPolicy_deterministic
    (data : VIPublicData E) (bcall : BorelCappedExactJetCall data) :
    (bcall.toPolicy data).IsDeterministic := by
  change Nonempty PUnit ∧ Subsingleton PUnit
  exact ⟨⟨PUnit.unit⟩, inferInstance⟩

/-- A finished execution against the genuine exact oracle becomes a genuine
unpadded run of the compiled policy.  The number of calls and projected output
are definitionally the same; no padded suffix is executed. -/
theorem BorelCappedExactJetCall.toPolicy_isUnpaddedRun_of_execute
    (data : VIPublicData E) (bcall : BorelCappedExactJetCall data)
    (F : E → E) (oracle : ExactSymmetricJetOracle data F)
    {used : ℕ} {result : Option (EvaluatedNormalCertificate data)}
    (hrun : bcall.call.execute data F (oracle.onFeasible data F) =
      .finished used result) :
    ∃ hn : used ≤ bcall.call.cap,
      ∃ history : OracleHistory data.X (SymmetricExactJet E data.p) used,
        (bcall.toPolicy data).IsUnpaddedRun oracle.answer PUnit.unit
          used hn history (certifiedCallOutput data bcall.fallback result) := by
  have hused : used ≤ bcall.call.cap :=
    bcall.call.finished_queries_le_cap data F (oracle.onFeasible data F) hrun
  have heval : ExactJetProgram.Evaluates (oracle.onFeasible data F).answer
      bcall.call.program used result :=
    ExactJetProgram.evaluates_of_runWithFuel_finished hrun
  have hcapped : ExactJetProgram.Evaluates (oracle.onFeasible data F).answer
      (bcall.call.program.locallyCapped bcall.call.cap) used result :=
    heval.locallyCapped hused
  obtain ⟨history, hreplayed⟩ := hcapped.exists_isReplayedRun
    (certifiedCallOutput data bcall.fallback)
  refine ⟨hused, history, ?_⟩
  simpa [BorelStoppingPolicy.IsUnpaddedRun,
    BorelCappedExactJetCall.toPolicy, ExactJetProgram.IsReplayedRun,
    ExactSymmetricJetOracle.onFeasible] using hreplayed

/-- Feasible-oracle version of operational preservation.  Unlike the legacy
ambient-oracle statement, this theorem needs no regularity outside `data.X`. -/
theorem BorelCappedExactJetCall.toPolicy_isUnpaddedRun_of_feasible_execute
    (data : VIPublicData E) (bcall : BorelCappedExactJetCall data)
    (F : E → E) (oracle : FeasibleExactSymmetricJetOracle data F)
    {used : ℕ} {result : Option (EvaluatedNormalCertificate data)}
    (hrun : bcall.call.execute data F oracle = .finished used result) :
    ∃ hn : used ≤ bcall.call.cap,
      ∃ history : OracleHistory data.X (SymmetricExactJet E data.p) used,
        (bcall.toPolicy data).IsUnpaddedRun
          (oracle.totalAnswer data F bcall.fallback) PUnit.unit used hn history
          (certifiedCallOutput data bcall.fallback result) := by
  have hused : used ≤ bcall.call.cap :=
    bcall.call.finished_queries_le_cap data F oracle hrun
  have heval : ExactJetProgram.Evaluates oracle.answer
      bcall.call.program used result :=
    ExactJetProgram.evaluates_of_runWithFuel_finished hrun
  have hcapped : ExactJetProgram.Evaluates oracle.answer
      (bcall.call.program.locallyCapped bcall.call.cap) used result :=
    heval.locallyCapped hused
  obtain ⟨history, hreplayed⟩ := hcapped.exists_isReplayedRun
    (certifiedCallOutput data bcall.fallback)
  refine ⟨hused, history, ?_⟩
  simpa [BorelStoppingPolicy.IsUnpaddedRun,
    BorelCappedExactJetCall.toPolicy, ExactJetProgram.IsReplayedRun] using
      hreplayed

/-- Successful certified execution yields the same saved point and the same
query count in the source-facing Borel policy. -/
theorem BorelCappedExactJetCall.toPolicy_successful_run
    (data : VIPublicData E) (bcall : BorelCappedExactJetCall data)
    (F : E → E) (oracle : ExactSymmetricJetOracle data F)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (hrun : bcall.call.execute data F (oracle.onFeasible data F) =
      .finished used (some cert)) :
    ∃ hn : used ≤ bcall.call.cap,
      ∃ history : OracleHistory data.X (SymmetricExactJet E data.p) used,
        (bcall.toPolicy data).IsUnpaddedRun oracle.answer PUnit.unit
          used hn history cert.point := by
  simpa [certifiedCallOutput] using
    bcall.toPolicy_isUnpaddedRun_of_execute data F oracle hrun

/-- Combining operational preservation with a verified certificate gives the
actual `def:policy` success predicate, not a certificate premise disguised as
algorithmic success. -/
theorem BorelCappedExactJetCall.toPolicy_runSucceedsOn
    (data : VIPublicData E) (bcall : BorelCappedExactJetCall data)
    (F : E → E) (oracle : ExactSymmetricJetOracle data F) (epsilon : ℝ)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (hrun : bcall.call.execute data F (oracle.onFeasible data F) =
      .finished used (some cert))
    (hcert : cert.IsVerifiedFor data F epsilon) :
    ∃ hn : used ≤ bcall.call.cap,
      ∃ history : OracleHistory data.X (SymmetricExactJet E data.p) used,
        (bcall.toPolicy data).RunSucceedsOn data F epsilon oracle PUnit.unit
          used hn history cert.point := by
  obtain ⟨hn, history, hpolicyRun⟩ :=
    bcall.toPolicy_successful_run data F oracle hrun
  exact ⟨hn, history, hpolicyRun,
    cert.tangentResidual_le data F epsilon hcert⟩

/-- End-to-end admissible-operator bridge.  Admissibility itself constructs
the exact symmetric feasible oracle, so neither a global oracle nor a
separate symmetry premise appears in the theorem. -/
theorem BorelCappedExactJetCall.toPolicy_runSucceedsOn_admissible
    (data : VIPublicData E) (bcall : BorelCappedExactJetCall data)
    (F : E → E) (hF : IsAdmissibleOperator data F) (epsilon : ℝ)
    {used : ℕ} {cert : EvaluatedNormalCertificate data}
    (hrun : bcall.call.execute data F
      (hF.feasibleExactSymmetricJetOracle data F) =
        .finished used (some cert))
    (hcert : cert.IsVerifiedFor data F epsilon) :
    ∃ hn : used ≤ bcall.call.cap,
      ∃ history : OracleHistory data.X (SymmetricExactJet E data.p) used,
        (bcall.toPolicy data).RunSucceedsOnFeasible data F epsilon
          (hF.feasibleExactSymmetricJetOracle data F) bcall.fallback PUnit.unit
          used hn history cert.point := by
  obtain ⟨hn, history, hrun'⟩ :=
    bcall.toPolicy_isUnpaddedRun_of_feasible_execute data F
      (hF.feasibleExactSymmetricJetOracle data F) hrun
  exact ⟨hn, history, hrun',
    cert.tangentResidual_le data F epsilon hcert⟩

section FamilyBridge

/-- Every public call selected by a residual family has a Borel replay rule,
with its supplied center used as the total feasible failure output. -/
def ResidualSolverFamily.IsBorel {p : ℕ}
    (family : ResidualSolverFamily.{u} p) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (data : VIPublicData E) (hp : data.p = p) (center : data.X)
    (R epsilon : ℝ),
      ((family.atData data hp).solve center R epsilon).IsBorel data center

/-- Strong-solver analogue of `ResidualSolverFamily.IsBorel`; every public
`(center, mu, delta)` call is audited independently of the unknown operator. -/
def StrongSolverFamily.IsBorel {p : ℕ}
    (family : StrongSolverFamily.{u} p) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (data : VIPublicData E) (hp : data.p = p) (center : data.X)
    (mu delta : ℝ),
      ((family.atData data hp).solve center mu delta).IsBorel data center

/-- Package any call of a Borel residual family as the source-facing capped
call, without changing its program or cap. -/
def ResidualSolverFamily.borelCall {p : ℕ}
    (family : ResidualSolverFamily.{u} p)
    (hfamily : family.IsBorel) (data : VIPublicData E) (hp : data.p = p)
    (center : data.X) (R epsilon : ℝ) : BorelCappedExactJetCall data where
  call := (family.atData data hp).solve center R epsilon
  fallback := center
  action_measurable := hfamily E data hp center R epsilon

def StrongSolverFamily.borelCall {p : ℕ}
    (family : StrongSolverFamily.{u} p)
    (hfamily : family.IsBorel) (data : VIPublicData E) (hp : data.p = p)
    (center : data.X) (mu delta : ℝ) : BorelCappedExactJetCall data where
  call := (family.atData data hp).solve center mu delta
  fallback := center
  action_measurable := hfamily E data hp center mu delta

/-- End-to-end family-level operational bridge.  The policy is compiled from
the very same capped program used by the residual interface; its genuine run
therefore has the same query count, while the interface supplies the original
certificate and cost bound. -/
theorem ResidualSolverFamily.borelPolicy_succeeds {p : ℕ}
    (family : ResidualSolverFamily.{u} p) (hfamily : family.IsBorel)
    (alpha : ℝ) (b : ℕ) (hinterface : family.SatisfiesInterface alpha b)
    (data : VIPublicData E) (hp : data.p = p)
    (F : E → E) (hF : IsAdmissibleOperator data F)
    (center : data.X) (R epsilon : ℝ)
    (hR : 0 < R) (hRD : R ≤ data.D) (hepsilon : 0 < epsilon)
    (zStar : E) (hz : IsVISolution data F zStar)
    (hdist : ‖center.1 - zStar‖ ≤ R) :
    ∃ used : ℕ, ∃ cert : EvaluatedNormalCertificate data,
      ∃ hn : used ≤ (family.borelCall hfamily data hp center R epsilon).call.cap,
        ∃ history : OracleHistory data.X (SymmetricExactJet E data.p) used,
          BorelStoppingPolicy.RunSucceedsOnFeasible data F epsilon
                ((family.borelCall hfamily data hp center R epsilon).toPolicy data)
                (hF.feasibleExactSymmetricJetOracle data F) center PUnit.unit used hn
                history cert.point ∧
          (used : ℝ) ≤ residualInterfaceCost data family.leadingConstant
            alpha b R epsilon := by
  let oracle := hF.feasibleExactSymmetricJetOracle data F
  obtain ⟨used, cert, hrun, hcert, hcost⟩ :=
    (hinterface E data hp).2.2 F oracle center R epsilon hF hR hRD hepsilon
      zStar hz hdist
  let bcall := family.borelCall hfamily data hp center R epsilon
  have hrun' : bcall.call.execute data F oracle =
      .finished used (some cert) := by
    simpa [bcall, ResidualSolverFamily.borelCall] using hrun
  obtain ⟨hn, history, hpolicy⟩ :=
    bcall.toPolicy_runSucceedsOn_admissible data F hF epsilon hrun' hcert
  exact ⟨used, cert, hn, history, hpolicy, hcost⟩

end FamilyBridge

end Compiler

end

end VIReference.Pilot
