import Bilevel.PolishedHistoryDeterministicRepresentation

/-! A call-clock augmentation is available for every public deterministic
program. It changes no query, output, or original-call count, and its clock
is the transition number at every live state of an actual experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedHistory
set_option autoImplicit false
variable {S Q O Y Ω : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace Ω]
variable (A : BorelAdaptive.Program S Q O Y)

def clockedProgram : BorelAdaptive.Program (S × ℕ) Q O Y where
  query := fun z => A.query z.1
  query_measurable := A.query_measurable.comp measurable_fst
  update := fun z => (A.update (z.1.1,z.2),z.1.2+1)
  update_measurable := (A.update_measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).add_const 1)
  halt := fun z => A.halt z.1
  halt_measurable := A.halt_measurable.comp measurable_fst
  output := fun z => A.output z.1
  output_measurable := A.output_measurable.comp measurable_fst

def experimentClock (state : ℕ → Ω → S) : ℕ → Ω → ℕ
  | 0 => fun _ => 0
  | n+1 => fun ω => experimentClock state n ω+if A.halt (state n ω)=true then 0 else 1

theorem experimentClock_measurable (state : ℕ → Ω → S)
    (hs : ∀ n,Measurable (state n)) (n : ℕ) : Measurable (experimentClock A state n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact ih.add (measurable_const.ite
        ((A.halt_measurable.comp (hs n)) (measurableSet_singleton true)) measurable_const)

def clockedState (state : ℕ → Ω → S) (n : ℕ) (ω : Ω) : S × ℕ :=
  (state n ω,experimentClock A state n ω)

theorem clockedState_measurable (state : ℕ → Ω → S)
    (hs : ∀ n,Measurable (state n)) (n : ℕ) : Measurable (clockedState A state n) :=
  (hs n).prodMk (experimentClock_measurable A state hs n)

variable {μ : Measure Ω}

/-- Absorbing actual dynamics make the call clock equal to `n` whenever the
program is still live at transition `n`. -/
theorem clockedState_live_clock (state : ℕ → Ω → S) (obs : ℕ → Ω → O)
    (hnext : ∀ n,∀ᵐ ω ∂μ,state (n+1) ω=
      if A.halt (state n ω)=true then state n ω else A.update (state n ω,obs n ω))
    (n : ℕ) : ∀ᵐ ω ∂μ,(clockedProgram A).halt (clockedState A state n ω)=false →
      (clockedState A state n ω).2=n := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun _ _ => rfl)
  | succ n ih =>
      filter_upwards [ih,hnext n] with ω hω hn hh
      change A.halt (state (n+1) ω)=false at hh
      have hlive : A.halt (state n ω)=false := by
        cases he : A.halt (state n ω) with
        | false => rfl
        | true =>
            have hs : state (n+1) ω=state n ω := by simpa only [he,if_true] using hn
            rw [hs,he] at hh
            contradiction
      change experimentClock A state n ω+(if A.halt (state n ω)=true then 0 else 1)=n+1
      have hcnt : experimentClock A state n ω=n := hω hlive
      rw [hcnt,hlive]
      rfl

theorem clockedState_next (state : ℕ → Ω → S) (obs : ℕ → Ω → O)
    (hnext : ∀ n,∀ᵐ ω ∂μ,state (n+1) ω=
      if A.halt (state n ω)=true then state n ω else A.update (state n ω,obs n ω))
    (n : ℕ) : ∀ᵐ ω ∂μ,clockedState A state (n+1) ω=
      if (clockedProgram A).halt (clockedState A state n ω)=true
      then clockedState A state n ω
      else (clockedProgram A).update (clockedState A state n ω,obs n ω) := by
  filter_upwards [hnext n] with ω hω
  cases hh : A.halt (state n ω) with
  | true => simp [clockedState,experimentClock,clockedProgram,hh] at hω ⊢; exact hω
  | false => simp [clockedState,experimentClock,clockedProgram,hh] at hω ⊢; exact hω

omit [MeasurableSpace Ω] in
theorem clockedState_stopped_calls (state : ℕ → Ω → S) (ω : Ω) :
    HistoryProgram.totalCalls (clockedProgram A) (experimentPath (clockedState A state) ω)=
      HistoryProgram.totalCalls A (experimentPath state ω) := rfl

omit [MeasurableSpace Ω] in
theorem clockedState_stopped_output (state : ℕ → Ω → S) (ω : Ω) :
    HistoryProgram.stoppedOutput (clockedProgram A) (experimentPath (clockedState A state) ω)=
      HistoryProgram.stoppedOutput A (experimentPath state ω) := rfl

end Bilevel.PolishedHistory
