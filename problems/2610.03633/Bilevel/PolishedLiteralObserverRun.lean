import Bilevel.PolishedLiteralActualObserver

/-! The selected observer is an implementation of an actual absorbing
algorithm run. Its integer credit is consumed only by new columns, so a
large number of oracle calls does not enlarge the frame budget. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior TransportControllerMachine SourceFrameActions
set_option autoImplicit false
variable {K d : ℕ} {C S Q O Y : Type}
  [MeasurableSpace C] [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y]
  (P : PrefixSchedule K) (hK : 0<K)
  (A : BorelAdaptive.Program S Q O Y)
  (evaluate : C → Q → ℕ → Bool → Frame d K → O)
  (heval : Measurable (fun z : C × (Q × (ℕ × (Bool × Frame d K))) =>
    evaluate z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2))
  (first second : Q → Space d) (hfirst : Measurable first) (hsecond : Measurable second)
  (output : Y → Space d) (houtput : Measurable output)

abbrev observerRules := rules P hK A evaluate heval first second hfirst hsecond output houtput

def credit (h : ObserverMemory C S d K) : ℕ := K-P.count h.2.2.2.1

theorem request_credit (t : ℕ) (h : ObserverMemory C S d K)
    (hr : (observerRules P hK A evaluate heval first second hfirst hsecond output houtput).request t h=true) :
    0<credit P h := by
  have hg : P.count h.2.2.2.1<P.count (h.2.2.2.1+1) := (of_decide_eq_true hr).2.2
  have := P.bound (h.2.2.2.1+1)
  dsimp [credit]
  omega

theorem step_counter_mono (t : ℕ) (h : ObserverMemory C S d K) (U : Frame d K) :
    h.2.2.2.1≤(step (observerRules P hK A evaluate heval first second hfirst hsecond output houtput) t h U).2.2.2.1 := by
  change h.2.2.2.1≤(finish P hK A evaluate t _).2.2.2.1
  by_cases hh : A.halt h.2.2.1=true
  · simp only [finish,if_pos hh,le_refl]
  · simp only [finish,if_neg hh]
    omega

theorem step_credit_nonincrease (t : ℕ) (h : ObserverMemory C S d K) (U : Frame d K) :
    credit P (step (observerRules P hK A evaluate heval first second hfirst hsecond output houtput) t h U)≤credit P h :=
  Nat.sub_le_sub_left (P.monotone (step_counter_mono P hK A evaluate heval first second hfirst hsecond output houtput t h U)) K

theorem step_credit_decrease (t : ℕ) (h : ObserverMemory C S d K) (U : Frame d K)
    (hr : (observerRules P hK A evaluate heval first second hfirst hsecond output houtput).request t h=true) :
    credit P (step (observerRules P hK A evaluate heval first second hfirst hsecond output houtput) t h U)+1≤credit P h := by
  have hh : A.halt h.2.2.1=false := (of_decide_eq_true hr).1
  have hb : h.2.1 t=true := (of_decide_eq_true hr).2.1
  have hg : P.count h.2.2.2.1<P.count (h.2.2.2.1+1) := (of_decide_eq_true hr).2.2
  change K-P.count (finish P hK A evaluate t _).2.2.2.1+1≤K-P.count h.2.2.2.1
  simp only [finish,hh,Bool.false_eq_true,if_false,hb,if_true]
  have := P.one_step h.2.2.2.1
  have := P.bound (h.2.2.2.1+1)
  omega

/-- The source observer requires no inequality between calls and columns. -/
theorem raw_safe_source_observed (cap : ℝ) (n R t : ℕ)
    (s : SourceFrameActions.State (ObserverMemory C S d K) d K) (U : Frame d K)
    (hc : credit P s.1≤R)
    (hs : OrdinaryFrame.Observed
      (compileRules (observerRules P hK A evaluate heval first second hfirst hsecond output houtput))
      cap n R t ((s.1,false),s.2) U) :
    SourceObserved (observerRules P hK A evaluate heval first second hfirst hsecond output houtput) cap n t s U := by
  apply compiled_source_observed_of_credit _ cap (credit P)
    (request_credit P hK A evaluate heval first second hfirst hsecond output houtput)
    (step_credit_decrease P hK A evaluate heval first second hfirst hsecond output houtput)
    (fun t h U _ => step_credit_nonincrease P hK A evaluate heval first second hfirst hsecond output houtput t h U)
    n R t s U hc hs

/-- A public state and its flat success counter, with the selected columns
stored only up to the schedule's disclosed prefix. -/
def lift (c : C) (draws : ℕ → Bool) (s : S × ℕ) (U : Frame d K) : ObserverMemory C S d K :=
  (c,(draws,(s.1,(s.2,prefixColumns U (P.count s.2)))))

/-- This is the actual algorithm update: the reply uses the old counter,
and its arrays may contain the newly disclosed column after a success. -/
def publicStep (c : C) (draws : ℕ → Bool) (U : Frame d K) (t : ℕ) (s : S × ℕ) : S × ℕ :=
  if A.halt s.1=true then s else
    let b := draws t
    let a' := s.2+if b=true then 1 else 0
    (A.update (s.1,evaluate c (A.query s.1) s.2 b (prefixColumns U (P.count a'))),a')

def publicRun (c : C) (draws : ℕ → Bool) (U : Frame d K) : ℕ → ℕ → S × ℕ → S × ℕ
  | 0,_,s => s
  | n+1,t,s => publicRun c draws U n (t+1) (publicStep P A evaluate c draws U t s)

theorem step_lift (c : C) (draws : ℕ → Bool) (s : S × ℕ) (U : Frame d K) (t : ℕ) :
    step (observerRules P hK A evaluate heval first second hfirst hsecond output houtput)
      t (lift P c draws s U) U = lift P c draws (publicStep P A evaluate c draws U t s) U := by
  by_cases hh : A.halt s.1=true
  · simp only [step,observerRules,rules,finish,lift,hh,if_true,publicStep]
  · have hhf : A.halt s.1=false := Bool.eq_false_iff.mpr hh
    have hr : request P A t (lift P c draws s U)=
        decide (P.count s.2<P.count (s.2+1) ∧ draws t=true) := by
      simp only [request,lift,hhf,Bool.false_eq_true,decide_true,true_and]
      congr 1
      exact propext and_comm
    have hu := P.update_actual hK s.2 (draws t) U
    change finish P hK A evaluate t
      (lift P c draws s U,if request P A t (lift P c draws s U)=true then U (P.nextIndex hK s.2) else 0)=_
    rw [hr]
    simp only [decide_eq_true_eq] 
    simp only [finish,lift,hh,if_false,publicStep]
    rw [hu]
    simp only [hhf,Bool.false_eq_true,if_false]

/-- Exact pathwise equality with the public virtual execution, including
its query states and its terminal output. -/
theorem run_lift (c : C) (draws : ℕ → Bool) (U : Frame d K) :
    ∀ n t (s : S × ℕ),
    run (observerRules P hK A evaluate heval first second hfirst hsecond output houtput)
      n t (lift P c draws s U) U = lift P c draws (publicRun P A evaluate c draws U n t s) U := by
  intro n
  induction n with
  | zero => intros;rfl
  | succ n ih =>
    intro t s
    rw [run,step_lift,publicRun,ih]

end Bilevel.PolishedLiteralActualObserver
