import Bilevel.SourceFrameEnergyEvent

/-! A source frame may be queried many more times than it has columns.
The compiler consumes only actual revelations, not inactive calls. A
decreasing integer credit proves that its fixed column budget suffices. -/
noncomputable section
universe u
namespace Bilevel.SourceFrameActions
open EuclideanGaussian ProjectionPosterior TransportControllerMachine
variable {H : Memory.{u}} {d T : ℕ}

theorem compiled_source_observed_of_credit (L : Rules H d T) (cap : ℝ)
    (credit : H → ℕ)
    (hrequest : ∀ t h,L.request t h=true → 0<credit h)
    (hyes : ∀ t h U,L.request t h=true → credit (step L t h U)+1≤credit h)
    (hno : ∀ t h U,L.request t h≠true → credit (step L t h U)≤credit h) :
    ∀ n R t (s : State H d T) (U : Frame d T), credit s.1≤R →
      OrdinaryFrame.Observed (compileRules L) cap n R t ((s.1,false),s.2) U →
      SourceObserved L cap n t s U := by
  intro n
  induction n with
  | zero => intros;assumption
  | succ n ih =>
    intro R t s U hcredit h
    have hncredit : credit (step L t s.1 U)≤credit s.1 := by
      by_cases hr : L.request t s.1=true
      · exact (Nat.le_add_right _ 1).trans (hyes t s.1 U hr)
      · exact hno t s.1 U hr
    cases R with
    | zero =>
      refine ⟨h.1,?_⟩
      have hr : L.request t s.1≠true := by
        intro hr
        have := hrequest t s.1 hr
        omega
      apply ih 0 (t+1) (observeStep L t s U) U
      · rw [observeStep_memory]
        omega
      · simpa only [observeStep,step,if_neg hr,OrdinaryFrame.precoin,
          OrdinaryFrame.queryStep,compileRules,mark] using h.2
    | succ R =>
      refine ⟨h.1,?_⟩
      by_cases hr : L.request t s.1=true
      · have hs : (OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1 ∈
            (compileRules L).success t := by
          change (OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1.2=true
          rw [precoin_memory]
          simp only [mark,if_pos hr]
        have hn := h.2
        rw [if_pos hs] at hn
        apply ih R (t+1) (observeStep L t s U) U
        · rw [observeStep_memory]
          have := hyes t s.1 U hr
          omega
        · simpa only [observeStep,step,if_pos hr,OrdinaryFrame.revealStep,OrdinaryFrame.precoin,
            OrdinaryFrame.queryStep,compileRules,mark] using hn
      · have hs : ¬(OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1 ∈
            (compileRules L).success t := by
          change ¬(OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1.2=true
          rw [precoin_memory]
          simp only [mark,if_neg hr,Bool.false_eq_true,not_false_eq_true]
        have hn := h.2
        rw [if_neg hs] at hn
        apply ih (R+1) (t+1) (observeStep L t s U) U
        · rw [observeStep_memory]
          omega
        · simpa only [observeStep,step,if_neg hr,OrdinaryFrame.precoin,
            OrdinaryFrame.queryStep,compileRules,mark] using hn

end Bilevel.SourceFrameActions
