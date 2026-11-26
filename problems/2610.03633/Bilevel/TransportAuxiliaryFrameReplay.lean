import Bilevel.TransportAuxiliaryFrameRun

/-! The selected auxiliary frame is accessed only through the requested
column argument. All complementary frames are immutable independent
context. The compiled source run is exactly the actual prefix-store run. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportAuxiliaryFrame
open EuclideanGaussian TransportControllerMachine
set_option autoImplicit false

abbrev SelectedMemory (C : Type u) (S : Type v) [MeasurableSpace C] [MeasurableSpace S]
    (k T D : ℕ) := Memory.of (Columns k T D × State C S k T D)

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {k T D B : ℕ}

def channel (P : Schedule k T) (t : ℕ) (i : Fin k) (U : Columns k T D)
    (y : Space D) : Fin k → Space D := Function.update (replies P t U) i y

theorem channel_actual (P : Schedule k T) (t : ℕ) (i : Fin k)
    (V U : Columns k T D) (hVU : ∀ j, j ≠ i → V j = U j) :
    channel P t i V (replies P t U i) = replies P t U := by
  funext j
  by_cases hj : j=i
  · subst j; exact Function.update_self _ _ _
  · rw [channel,Function.update_of_ne hj]
    simp only [replies,hVU j hj]

theorem channel_measurable (P : Schedule k T) (t : ℕ) (i : Fin k) :
    Measurable (fun p : Columns k T D × Space D => channel P t i p.1 p.2) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j=i
  · subst j; simpa only [channel,Function.update_self] using
      (measurable_snd : Measurable (fun p : Columns k T D × Space D => p.2))
  · simpa only [channel,Function.update_of_ne hj] using
      ((measurable_pi_apply j).comp (replies_measurable P t)).comp
        (measurable_fst : Measurable (fun p : Columns k T D × Space D => p.1))

def selectedFinish (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k)
    (t : ℕ) (p : SelectedMemory C S k T D × Space D) : SelectedMemory C S k T D :=
  let next := advance P t p.1.2.2.2 (channel P t i p.1.1 p.2)
  (p.1.1,(p.1.2.1,(A.respond t (p.1.2,next),next)))

theorem selectedFinish_measurable (P : Schedule k T) (A : Driver C S k T D B)
    (i : Fin k) (t : ℕ) : Measurable (selectedFinish P A i t) := by
  let Z := SelectedMemory C S k T D × Space D
  have hs : Measurable (fun p : Z => p.1.2) := measurable_snd.comp measurable_fst
  have hc : Measurable (fun p : Z => p.1.1) := measurable_fst.comp measurable_fst
  have hy := (channel_measurable P t i).comp (hc.prodMk (measurable_snd : Measurable (fun p : Z => p.2)))
  have hn := (advance_measurable P t).comp
    ((measurable_snd.comp (measurable_snd.comp hs)).prodMk hy)
  exact hc.prodMk ((measurable_fst.comp hs).prodMk
    (((A.respond_measurable t).comp (hs.prodMk hn)).prodMk hn))

def selectedRules (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k) :
    SourceFrameActions.Rules (SelectedMemory C S k T D) D (T+1) where
  first _ _ := 0
  first_measurable _ := measurable_const
  second _ _ := 0
  second_measurable _ := measurable_const
  request t _ := request P t i
  request_measurable _ := measurable_const
  column t _ := column P t i
  column_measurable _ := measurable_const
  finish := selectedFinish P A i
  finish_measurable := selectedFinish_measurable P A i
  output h := A.output h.2
  output_measurable := A.output_measurable.comp measurable_snd

theorem selected_step_actual (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k)
    (t : ℕ) (V U : Columns k T D) (hVU : ∀ j, j ≠ i → V j = U j)
    (s : State C S k T D) :
    SourceFrameActions.step (selectedRules P A i) t (V,s) (U i) =
      (V,step P A t s U) := by
  change (V,(s.1,(A.respond t (s,advance P t s.2.2
    (channel P t i V (replies P t U i))),advance P t s.2.2
    (channel P t i V (replies P t U i))))) = _
  rw [channel_actual P t i V U hVU]
  rfl

theorem selected_run_actual (P : Schedule k T) (A : Driver C S k T D B) (i : Fin k) :
    ∀ n t (V U : Columns k T D), (∀ j, j ≠ i → V j = U j) →
      ∀ s : State C S k T D,
      SourceFrameActions.run (selectedRules P A i) n t (V,s) (U i) =
        (V,run P A n t s U) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro t V U hVU s
    rw [SourceFrameActions.run,selected_step_actual P A i t V U hVU,
      ih (t+1) V U hVU,run]

def selectedQueries (A : Driver C S k T D B) (t : ℕ)
    (h : SelectedMemory C S k T D) : Fin B → Space D := A.queries t h.2

theorem selectedQueries_measurable (A : Driver C S k T D B) (t : ℕ) (b : Fin B) :
    Measurable (fun h : SelectedMemory C S k T D => selectedQueries A t h b) :=
  (A.queries_measurable t b).comp measurable_snd

def selectedBatchRules (P : Schedule k T) (A : Driver C S k T D B)
    (i : Fin k) (hB : 0 < B) : SourceFrameActions.Rules (SelectedMemory C S k T D) D (T+1) :=
  SourceFrameActions.batchRules (selectedRules P A i) hB (selectedQueries A) (selectedQueries_measurable A)

theorem selected_batch_run_actual (P : Schedule k T) (A : Driver C S k T D B)
    (i : Fin k) (hB : 0 < B) (n t : ℕ) (V U : Columns k T D)
    (hVU : ∀ j, j ≠ i → V j = U j) (s : State C S k T D) :
    SourceFrameActions.run (selectedBatchRules P A i hB) (n*B) (t*B) (V,s) (U i) =
      (V,run P A n t s U) := by
  rw [selectedBatchRules,SourceFrameActions.batch_run_blocks,
    selected_run_actual P A i n t V U hVU]

end Bilevel.TransportAuxiliaryFrame
