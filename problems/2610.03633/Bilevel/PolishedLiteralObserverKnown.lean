import Bilevel.PolishedLiteralObserverRun

/-! The actual named-column set never contains an undisclosed future
column. Thus the source observation event controls every future raw
coordinate at each actual query and at the arbitrary terminal output. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior TransportControllerMachine SourceFrameActions
set_option autoImplicit false
variable {K d : ℕ} {C S Q O Y : Type}
  [MeasurableSpace C] [MeasurableSpace S] [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
  (P : PrefixSchedule K) (hK : 0<K) (A : BorelAdaptive.Program S Q O Y)
  (evaluate : C → Q → ℕ → Bool → Frame d K → O)
  (heval : Measurable (fun z : C × (Q × (ℕ × (Bool × Frame d K))) =>
    evaluate z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2))
  (first second : Q → Space d) (hfirst : Measurable first) (hsecond : Measurable second)
  (output : Y → Space d) (houtput : Measurable output)

abbrev L := observerRules P hK A evaluate heval first second hfirst hsecond output houtput

def PrefixKnown (s : SourceFrameActions.State (ObserverMemory C S d K) d K) : Prop :=
  ∀ i∈s.2.2,i.val<P.count s.1.2.2.2.1

theorem step_prefixKnown (t : ℕ) (s : SourceFrameActions.State (ObserverMemory C S d K) d K)
    (U : Frame d K) (hs : PrefixKnown P s) :
    PrefixKnown P (observeStep (L P hK A evaluate heval first second hfirst hsecond output houtput) t s U) := by
  let LL := L P hK A evaluate heval first second hfirst hsecond output houtput
  have hmono := P.monotone (step_counter_mono P hK A evaluate heval first second hfirst hsecond output houtput t s.1 U)
  intro i hi
  by_cases hr : LL.request t s.1=true
  · have hh : A.halt s.1.2.2.1=false := (of_decide_eq_true hr).1
    have hb : s.1.2.1 t=true := (of_decide_eq_true hr).2.1
    have hg : P.count s.1.2.2.2.1<P.count (s.1.2.2.2.1+1) := (of_decide_eq_true hr).2.2
    have hbound : P.count s.1.2.2.2.1<K := hg.trans_le (P.bound _)
    change i∈(observeStep LL t s U).2.2 at hi
    simp only [observeStep,if_pos hr] at hi
    rw [observeStep_memory]
    rcases Set.mem_insert_iff.mp hi with hi | hi
    · subst i
      change (P.nextIndex hK s.1.2.2.2.1).val<P.count (finish P hK A evaluate t _).2.2.2.1
      simpa only [PrefixSchedule.nextIndex,dif_pos hbound,finish,hh,Bool.false_eq_true,if_false,hb,if_true] using hg
    · exact (hs i hi).trans_le hmono
  · change i∈(observeStep LL t s U).2.2 at hi
    simp only [observeStep,if_neg hr] at hi
    rw [observeStep_memory]
    exact (hs i hi).trans_le hmono

theorem run_prefixKnown : ∀ n t (s : SourceFrameActions.State (ObserverMemory C S d K) d K)
    (U : Frame d K), PrefixKnown P s →
    PrefixKnown P (observeRun (L P hK A evaluate heval first second hfirst hsecond output houtput) n t s U) := by
  intro n
  induction n with
  | zero => intros;assumption
  | succ n ih =>
    intro t s U hs
    exact ih (t+1) _ U
      (step_prefixKnown P hK A evaluate heval first second hfirst hsecond output houtput t s U hs)

theorem initial_prefixKnown (h : ObserverMemory C S d K) : PrefixKnown P (h,(⊥,∅)) := by
  intro i hi
  exact False.elim hi

theorem source_observed_query_inner (cap : ℝ) (hcap : 0≤cap) (n t k : ℕ)
    (s : SourceFrameActions.State (ObserverMemory C S d K) d K) (U : Frame d K)
    (hs : PrefixKnown P s) (hk : k<n)
    (ho : SourceObserved (L P hK A evaluate heval first second hfirst hsecond output houtput) cap n t s U)
    (i : Fin K) (hi : P.count
      (run (L P hK A evaluate heval first second hfirst hsecond output houtput) k t s.1 U).2.2.2.1 ≤ i.val) :
    |⟪U i,(L P hK A evaluate heval first second hfirst hsecond output houtput).first (t+k)
      (run (L P hK A evaluate heval first second hfirst hsecond output houtput) k t s.1 U)⟫|≤
      Real.sqrt cap*‖(L P hK A evaluate heval first second hfirst hsecond output houtput).first (t+k)
        (run (L P hK A evaluate heval first second hfirst hsecond output houtput) k t s.1 U)‖ ∧
    |⟪U i,(L P hK A evaluate heval first second hfirst hsecond output houtput).second (t+k)
      (run (L P hK A evaluate heval first second hfirst hsecond output houtput) k t s.1 U)⟫|≤
      Real.sqrt cap*‖(L P hK A evaluate heval first second hfirst hsecond output houtput).second (t+k)
        (run (L P hK A evaluate heval first second hfirst hsecond output houtput) k t s.1 U)‖ := by
  let LL := L P hK A evaluate heval first second hfirst hsecond output houtput
  let st := observeRun LL k t s U
  have he := source_observed_at LL cap k n t s U hk ho
  have hn : i∉st.2.2 := by
    intro hm
    have hp := run_prefixKnown P hK A evaluate heval first second hfirst hsecond output houtput k t s U hs i hm
    rw [observeRun_memory] at hp
    omega
  have hf : LL.first (t+k) st.1∈querySpace LL (t+k) st :=
    Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hg : LL.second (t+k) st.1∈querySpace LL (t+k) st :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hb := OrdinaryFrame.boundedEnergy_inner _ _ U cap hcap he _ hf i hn
  have hc := OrdinaryFrame.boundedEnergy_inner _ _ U cap hcap he _ hg i hn
  simpa only [st,observeRun_memory] using And.intro hb hc

theorem source_observed_output_inner (cap : ℝ) (hcap : 0≤cap) (n t : ℕ)
    (s : SourceFrameActions.State (ObserverMemory C S d K) d K) (U : Frame d K)
    (hs : PrefixKnown P s)
    (ho : SourceObserved (L P hK A evaluate heval first second hfirst hsecond output houtput) cap n t s U)
    (i : Fin K) (hi : P.count
      (run (L P hK A evaluate heval first second hfirst hsecond output houtput) n t s.1 U).2.2.2.1 ≤ i.val) :
    |⟪U i,(L P hK A evaluate heval first second hfirst hsecond output houtput).output
      (run (L P hK A evaluate heval first second hfirst hsecond output houtput) n t s.1 U)⟫|≤
      Real.sqrt cap*‖(L P hK A evaluate heval first second hfirst hsecond output houtput).output
        (run (L P hK A evaluate heval first second hfirst hsecond output houtput) n t s.1 U)‖ := by
  let LL := L P hK A evaluate heval first second hfirst hsecond output houtput
  let st := observeRun LL n t s U
  have he := source_observed_final LL cap n t s U ho
  have hn : i∉st.2.2 := by
    intro hm
    have hp := run_prefixKnown P hK A evaluate heval first second hfirst hsecond output houtput n t s U hs i hm
    rw [observeRun_memory] at hp
    omega
  have hf : LL.output st.1∈(finishObservation LL st).2.1 :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hb := OrdinaryFrame.boundedEnergy_inner _ _ U cap hcap he _ hf i hn
  simpa only [st,observeRun_memory] using hb

end Bilevel.PolishedLiteralActualObserver
