import Bilevel.BorelAdaptiveExtendedCalls

/-! An actual measurable change of oracle channels preserves every state,
terminal output, and original-call count, including nontermination. -/
noncomputable section
namespace Bilevel.BorelAdaptive
set_option autoImplicit false
variable {S Q O Q' O' Y I C Private : Type*}
  [MeasurableSpace S] [MeasurableSpace Q] [MeasurableSpace O]
  [MeasurableSpace Q'] [MeasurableSpace O'] [MeasurableSpace Y]

/-- Run an original program through a query encoder and a reply decoder. -/
def channelProgram (A : Program S Q O Y) (encode : Q → Q') (decode : O' → O)
    (he : Measurable encode) (hd : Measurable decode) : Program S Q' O' Y where
  query := encode ∘ A.query
  query_measurable := he.comp A.query_measurable
  update := fun z => A.update (z.1,decode z.2)
  update_measurable := A.update_measurable.comp (measurable_fst.prodMk (hd.comp measurable_snd))
  halt := A.halt
  halt_measurable := A.halt_measurable
  output := A.output
  output_measurable := A.output_measurable

variable (A : Program S Q O Y) (encode : Q → Q') (decode : O' → O)
  (he : Measurable encode) (hd : Measurable decode)
  (original : I → Q → C → O) (encoded : I → Q' → C → O')
  (hreplies : ∀ i q c,decode (encoded i (encode q) c)=original i q c)

include hreplies

theorem channel_step (i : I) (c : C) (s : S) :
    step (channelProgram A encode decode he hd) encoded i c s=step A original i c s := by
  simp only [step,channelProgram,Function.comp_apply,hreplies]

theorem channel_run (i : I) (draws : ℕ → C) (s : S) (n : ℕ) :
    run (channelProgram A encode decode he hd) encoded i draws s n=run A original i draws s n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run,run,ih,channel_step A encode decode he hd original encoded hreplies]

theorem channel_terminated (p : Sample I S C) :
    Terminated (channelProgram A encode decode he hd) encoded p ↔ Terminated A original p := by
  change (∃ n,A.halt (run (channelProgram A encode decode he hd) encoded p.1 p.2.2 p.2.1 n)=true) ↔ _
  simp only [channel_run A encode decode he hd original encoded hreplies]
  rfl

theorem channel_stopTime (p : Sample I S C) :
    stopTime (channelProgram A encode decode he hd) encoded p=stopTime A original p := by
  classical
  unfold stopTime
  have ht := channel_terminated A encode decode he hd original encoded hreplies p
  split_ifs with h₁ h₂ h₂
  · apply Nat.find_congr'
    intro n
    change A.halt (run (channelProgram A encode decode he hd) encoded p.1 p.2.2 p.2.1 n)=true ↔ _
    rw [channel_run A encode decode he hd original encoded hreplies]
  · exact False.elim (h₂ (ht.mp h₁))
  · exact False.elim (h₁ (ht.mpr h₂))
  · rfl

theorem channel_cappedOutput (n : ℕ) (p : Sample I S C) :
    cappedOutput (channelProgram A encode decode he hd) encoded n p=cappedOutput A original n p := by
  change A.output (run (channelProgram A encode decode he hd) encoded p.1 p.2.2 p.2.1 n)=_
  rw [channel_run A encode decode he hd original encoded hreplies]
  rfl

theorem channel_stoppedOutput (p : Sample I S C) :
    stoppedOutput (channelProgram A encode decode he hd) encoded p=stoppedOutput A original p := by
  rw [stoppedOutput,stoppedOutput,channel_stopTime A encode decode he hd original encoded hreplies]
  exact channel_cappedOutput A encode decode he hd original encoded hreplies _ p

theorem channel_calls (i : I) (draws : ℕ → C) (s : S) (n : ℕ) :
    calls (channelProgram A encode decode he hd) encoded i draws s n=calls A original i draws s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [calls,ih,channel_run A encode decode he hd original encoded hreplies]
    rfl

theorem channel_totalCalls (p : Sample I S C) :
    totalCalls (channelProgram A encode decode he hd) encoded p=totalCalls A original p := by
  rw [totalCalls_eq_iSup_calls,totalCalls_eq_iSup_calls]
  simp only [channel_calls A encode decode he hd original encoded hreplies]

theorem channel_seededCalls (initial : Private → S) (p : Sample I Private C) :
    seededCalls (channelProgram A encode decode he hd) encoded initial p=seededCalls A original initial p :=
  channel_totalCalls A encode decode he hd original encoded hreplies _

theorem channel_seededStopped (initial : Private → S) (p : Sample I Private C) :
    seededStopped (channelProgram A encode decode he hd) encoded initial p=seededStopped A original initial p :=
  congrArg (Prod.mk p.1) (channel_stoppedOutput A encode decode he hd original encoded hreplies _)

end Bilevel.BorelAdaptive
