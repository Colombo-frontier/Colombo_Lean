import Nonsmooth.MeasurableSimulation
import Mathlib.Data.Fin.Tuple.Basic

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

abbrev History (X : Type) (n : ℕ) := Fin n → X × ℝ
abbrev HistoryStore (X : Type) := ℕ → X × ℝ

/-- Query maps have exactly the complete finite-history domains used in the manuscript. -/
structure HistoryPolicy (Ω X : Type) where
  query : (n : ℕ) → Ω → History X n → X
  output : (n : ℕ) → Ω → History X n → X

def HistoryPolicy.transcript {Ω X : Type} (p : HistoryPolicy Ω X) (f : X → ℝ) (ω : Ω) :
    (n : ℕ) → History X n
  | 0 => Fin.elim0
  | n + 1 => let h := p.transcript f ω n
    let x := p.query n ω h
    Fin.snoc h (x, f x)

def HistoryPolicy.result {Ω X : Type} (p : HistoryPolicy Ω X) (f : X → ℝ) (ω : Ω) (T : ℕ) : X :=
  p.output T ω (p.transcript f ω T)

def historyPrefix {X : Type} (n : ℕ) (st : HistoryStore X) : History X n := fun i => st i.val

def HistoryPolicy.toState {Ω X : Type} (p : HistoryPolicy Ω X) (T : ℕ) (x0 : X) :
    Policy Ω (HistoryStore X) X where
  initial _ _ := (x0, 0)
  query n ω st := p.query n ω (historyPrefix n st)
  update n ω st y := Function.update st n (p.query n ω (historyPrefix n st), y)
  output ω st := p.output T ω (historyPrefix T st)

theorem history_toState_transcript {Ω X : Type} (p : HistoryPolicy Ω X) (T : ℕ) (x0 : X)
    (f : X → ℝ) (ω : Ω) (n : ℕ) :
    historyPrefix n ((p.toState T x0).run f ω n) = p.transcript f ω n := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [historyPrefix, Policy.run, HistoryPolicy.toState, Fin.val_last,
        Function.update_self, HistoryPolicy.transcript, Fin.snoc_last]
      simpa only [HistoryPolicy.toState] using
        congrArg (fun h => (p.query n ω h, f (p.query n ω h))) ih
    · have hne : j.val ≠ n := Nat.ne_of_lt j.isLt
      simpa only [historyPrefix, Policy.run, HistoryPolicy.toState, Fin.coe_castSucc,
        Function.update_of_ne hne, HistoryPolicy.transcript, Fin.snoc_castSucc] using congr_fun ih j

theorem history_toState_result {Ω X : Type} (p : HistoryPolicy Ω X) (T : ℕ) (x0 : X)
    (f : X → ℝ) (ω : Ω) : (p.toState T x0).result f ω T = p.result f ω T := by
  change p.output T ω (historyPrefix T ((p.toState T x0).run f ω T)) = _
  rw [history_toState_transcript]
  rfl

/-- Evaluate the original state machine on any complete history, using its real responses. -/
def Policy.stateOnHistory {Ω S X : Type} (p : Policy Ω S X) (ω : Ω) :
    (n : ℕ) → History X n → S
  | 0, _ => p.initial ω
  | n + 1, h => p.update n ω (p.stateOnHistory ω n (Fin.init h)) (h (Fin.last n)).2

def Policy.toHistory {Ω S X : Type} (p : Policy Ω S X) : HistoryPolicy Ω X where
  query n ω h := p.query n ω (p.stateOnHistory ω n h)
  output n ω h := p.output ω (p.stateOnHistory ω n h)

theorem state_toHistory_run {Ω S X : Type} (p : Policy Ω S X) (f : X → ℝ) (ω : Ω) (n : ℕ) :
    p.stateOnHistory ω n (p.toHistory.transcript f ω n) = p.run f ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [HistoryPolicy.transcript, Policy.stateOnHistory, Fin.init_snoc, Fin.snoc_last,
      Policy.toHistory, Policy.run]
    simpa only [Policy.toHistory] using
      congrArg (fun st => p.update n ω st (f (p.query n ω st))) ih

theorem state_toHistory_result {Ω S X : Type} (p : Policy Ω S X) (f : X → ℝ) (ω : Ω) (T : ℕ) :
    p.toHistory.result f ω T = p.result f ω T := by
  change p.output ω (p.stateOnHistory ω T (p.toHistory.transcript f ω T)) = _
  rw [state_toHistory_run]
  rfl

variable {Ω S X : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace X]

structure HistoryPolicy.IsMeasurable (p : HistoryPolicy Ω X) : Prop where
  query : ∀ n, Measurable (fun z : Ω × History X n => p.query n z.1 z.2)
  output : ∀ n, Measurable (fun z : Ω × History X n => p.output n z.1 z.2)

theorem historyPrefix_measurable (n : ℕ) : Measurable (historyPrefix (X := X) n) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply i.val

theorem history_toState_measurable {p : HistoryPolicy Ω X} (hp : p.IsMeasurable) (T : ℕ) (x0 : X) :
    (p.toState T x0).IsMeasurable := by
  have hq (n : ℕ) : Measurable (fun z : Ω × HistoryStore X => p.query n z.1 (historyPrefix n z.2)) :=
    (hp.query n).comp (measurable_fst.prodMk ((historyPrefix_measurable n).comp measurable_snd))
  refine ⟨measurable_const, hq, ?_, ?_⟩
  · intro n
    have hs : Measurable (fun z : Ω × HistoryStore X × ℝ => z.2.1) := measurable_fst.comp measurable_snd
    have hy : Measurable (fun z : Ω × HistoryStore X × ℝ => z.2.2) := measurable_snd.comp measurable_snd
    have hx : Measurable (fun z : Ω × HistoryStore X × ℝ =>
        p.query n z.1 (historyPrefix n z.2.1)) := (hq n).comp (measurable_fst.prodMk hs)
    exact measurable_update'.comp (hs.prodMk (hx.prodMk hy))
  · exact (hp.output T).comp (measurable_fst.prodMk ((historyPrefix_measurable T).comp measurable_snd))

theorem stateOnHistory_measurable {p : Policy Ω S X} (hp : p.IsMeasurable) (n : ℕ) :
    Measurable (fun z : Ω × History X n => p.stateOnHistory z.1 n z.2) := by
  induction n with
  | zero => exact hp.initial.comp measurable_fst
  | succ n ih =>
    have hinit : Measurable (fun h : History X (n + 1) => Fin.init h) := by
      apply measurable_pi_iff.mpr
      intro i
      exact measurable_pi_apply i.castSucc
    have hs := ih.comp (measurable_fst.prodMk (hinit.comp measurable_snd))
    have hy : Measurable (fun z : Ω × History X (n + 1) => (z.2 (Fin.last n)).2) :=
      measurable_snd.comp ((measurable_pi_apply (Fin.last n)).comp measurable_snd)
    exact (hp.update n).comp (measurable_fst.prodMk (hs.prodMk hy))

theorem state_toHistory_measurable {p : Policy Ω S X} (hp : p.IsMeasurable) :
    p.toHistory.IsMeasurable :=
  ⟨fun n => (hp.query n).comp (measurable_fst.prodMk (stateOnHistory_measurable hp n)),
    fun n => hp.output.comp (measurable_fst.prodMk (stateOnHistory_measurable hp n))⟩

end
end Nonsmooth
