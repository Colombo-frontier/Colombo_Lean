import Geode.OracleReplay

/-! A semantic deterministic oracle model allowing internal divergence.
At each finite history, `none` means that the algorithm never produces its
next decision. Such a stall consumes no additional oracle query. -/
namespace Geode.OracleReplay

universe u v

structure PartialStoppingAlgorithm (Point : Type u) (Reply : Type v) where
  decide : History Point Reply → Option (Decision Point)

variable {Point : Type u} {Reply : Type v}

inductive PartialRunResult (Point : Type u) (Reply : Type v) where
  | finished : History Point Reply → Point → PartialRunResult Point Reply
  | exhausted : History Point Reply → Point → PartialRunResult Point Reply
  | stalled : History Point Reply → PartialRunResult Point Reply

def PartialRunResult.history : PartialRunResult Point Reply → History Point Reply
  | .finished h _ => h
  | .exhausted h _ => h
  | .stalled h => h

/-- Query fuel bounds actual calls to the oracle, independently of whether
the internal computation subsequently stops, stalls, or requests another call. -/
def partialRun (A : PartialStoppingAlgorithm Point Reply) (respond : Responder Point Reply) :
    ℕ → History Point Reply → PartialRunResult Point Reply
  | 0, h => match A.decide h with
    | none => .stalled h
    | some (.stop x) => .finished h x
    | some (.query x) => .exhausted h x
  | n + 1, h => match A.decide h with
    | none => .stalled h
    | some (.stop x) => .finished h x
    | some (.query x) => partialRun A respond n (h ++ [(x, respond h x)])

/-- A semantic totalization: replace an undefined next decision by a query.
No claim of computability of this transformation is needed by the lower bound. -/
def PartialStoppingAlgorithm.totalize (A : PartialStoppingAlgorithm Point Reply)
    (default : Point) : StoppingAlgorithm Point Reply where
  decide h := (A.decide h).getD (.query default)

theorem partial_finished_totalizes (A : PartialStoppingAlgorithm Point Reply)
    (default : Point) (respond : Responder Point Reply) (n : ℕ)
    (h finalHistory : History Point Reply) (output : Point)
    (hf : partialRun A respond n h = .finished finalHistory output) :
    run (A.totalize default) respond n h = .finished finalHistory output := by
  induction n generalizing h with
  | zero =>
    cases hd : A.decide h with
    | none => simp only [partialRun, hd] at hf; cases hf
    | some d =>
      cases d with
      | stop x =>
        have heq : PartialRunResult.finished h x = .finished finalHistory output := by
          simpa only [partialRun, hd] using hf
        obtain ⟨rfl, rfl⟩ := PartialRunResult.finished.inj heq
        simp only [run, PartialStoppingAlgorithm.totalize, hd, Option.getD_some]
      | query x => simp only [partialRun, hd] at hf; cases hf
  | succ n ih =>
    cases hd : A.decide h with
    | none => simp only [partialRun, hd] at hf; cases hf
    | some d =>
      cases d with
      | stop x =>
        have heq : PartialRunResult.finished h x = .finished finalHistory output := by
          simpa only [partialRun, hd] using hf
        obtain ⟨rfl, rfl⟩ := PartialRunResult.finished.inj heq
        simp only [run, PartialStoppingAlgorithm.totalize, hd, Option.getD_some]
      | query x =>
        simp only [run, PartialStoppingAlgorithm.totalize, hd, Option.getD_some]
        apply ih
        simpa only [partialRun, hd] using hf

/-- A stalled internal computation fails every budget-and-output guarantee,
just as a request beyond the query budget does. -/
def PartialRunFails (Fails : Point → Prop) : PartialRunResult Point Reply → Prop
  | .finished _ output => Fails output
  | .exhausted _ _ => True
  | .stalled _ => True

theorem totalized_failure_transfers (A : PartialStoppingAlgorithm Point Reply)
    (default : Point) (respond : Responder Point Reply) (n : ℕ)
    (h : History Point Reply) (Fails : Point → Prop)
    (hfail : RunFails Fails (run (A.totalize default) respond n h)) :
    PartialRunFails Fails (partialRun A respond n h) := by
  cases hr : partialRun A respond n h with
  | finished finalHistory output =>
    have hf := partial_finished_totalizes A default respond n h finalHistory output hr
    simpa only [hf, RunFails, PartialRunFails] using hfail
  | exhausted finalHistory nextQuery => trivial
  | stalled finalHistory => trivial

def StoppingAlgorithm.toPartial (A : StoppingAlgorithm Point Reply) :
    PartialStoppingAlgorithm Point Reply where
  decide h := some (A.decide h)

def RunResult.toPartial : RunResult Point Reply → PartialRunResult Point Reply
  | .finished h output => .finished h output
  | .exhausted h nextQuery => .exhausted h nextQuery

/-- Embedding an everywhere-defined decision rule preserves the entire run. -/
theorem partialRun_toPartial (A : StoppingAlgorithm Point Reply)
    (respond : Responder Point Reply) (n : ℕ) (h : History Point Reply) :
    partialRun A.toPartial respond n h = (run A respond n h).toPartial := by
  induction n generalizing h with
  | zero => cases hd : A.decide h <;>
      simp only [partialRun, StoppingAlgorithm.toPartial, run, hd, RunResult.toPartial]
  | succ n ih =>
    cases hd : A.decide h with
    | stop x => simp only [partialRun, StoppingAlgorithm.toPartial, run, hd, RunResult.toPartial]
    | query x =>
      simp only [partialRun, StoppingAlgorithm.toPartial, run, hd]
      exact ih _

theorem total_finished_embeds (A : StoppingAlgorithm Point Reply)
    (respond : Responder Point Reply) (n : ℕ) (h finalHistory : History Point Reply)
    (output : Point) (hf : run A respond n h = .finished finalHistory output) :
    partialRun A.toPartial respond n h = .finished finalHistory output := by
  rw [partialRun_toPartial, hf]
  rfl

end Geode.OracleReplay
