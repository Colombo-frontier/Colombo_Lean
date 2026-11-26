import Bilevel.SourceFrameObservation

/-! The raw-genie good event controls the query space before each named
reveal of the actual source action, as well as its terminal insertion. -/
noncomputable section
universe u
namespace Bilevel.SourceFrameActions
open EuclideanGaussian ProjectionPosterior TransportControllerMachine

variable {H : Memory.{u}} {d T : ℕ}

def querySpace (L : Rules H d T) (t : ℕ) (s : State H d T) : Submodule ℝ (Space d) :=
  (s.2.1 ⊔ Submodule.span ℝ {L.first t s.1}) ⊔ Submodule.span ℝ {L.second t s.1}

def SourceObserved (L : Rules H d T) (cap : ℝ) : ℕ → ℕ → State H d T → Frame d T → Prop
  | 0,_,s,U => GenieProtocol.BoundedEnergy (finishObservation L s).2.1 s.2.2 U cap
  | n+1,t,s,U => GenieProtocol.BoundedEnergy (querySpace L t s) s.2.2 U cap ∧
      SourceObserved L cap n (t+1) (observeStep L t s U) U

theorem compiled_source_observed (L : Rules H d T) (cap : ℝ) :
    ∀ n R t (s : State H d T) (U : Frame d T), n≤R →
      OrdinaryFrame.Observed (compileRules L) cap n R t ((s.1,false),s.2) U →
      SourceObserved L cap n t s U := by
  intro n
  induction n with
  | zero => intros; assumption
  | succ n ih =>
    intro R t s U hR h
    cases R with
    | zero => omega
    | succ R =>
      refine ⟨h.1,?_⟩
      have hn := h.2
      by_cases hr : L.request t s.1=true
      · have hs : (OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1 ∈
            (compileRules L).success t := by
          change (OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1.2=true
          rw [precoin_memory]
          simp only [mark,if_pos hr]
        rw [if_pos hs] at hn
        apply ih R (t+1) (observeStep L t s U) U (by omega)
        simpa only [observeStep,step,if_pos hr,OrdinaryFrame.revealStep,OrdinaryFrame.precoin,
          OrdinaryFrame.queryStep,compileRules,mark] using hn
      · have hs : ¬(OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1 ∈
            (compileRules L).success t := by
          change ¬(OrdinaryFrame.precoin (compileRules L) t ((s.1,false),s.2) U).1.2=true
          rw [precoin_memory]
          simp only [mark,if_neg hr,Bool.false_eq_true,not_false_eq_true]
        rw [if_neg hs] at hn
        apply ih (R+1) (t+1) (observeStep L t s U) U (by omega)
        simpa only [observeStep,step,if_neg hr,OrdinaryFrame.precoin,
          OrdinaryFrame.queryStep,compileRules,mark] using hn

theorem source_observed_at (L : Rules H d T) (cap : ℝ) :
    ∀ k n t (s : State H d T) (U : Frame d T), k<n → SourceObserved L cap n t s U →
      GenieProtocol.BoundedEnergy (querySpace L (t+k) (observeRun L k t s U))
        (observeRun L k t s U).2.2 U cap := by
  intro k
  induction k with
  | zero =>
    intro n t s U hk h
    cases n with
    | zero => omega
    | succ n => simpa only [Nat.add_zero,observeRun] using h.1
  | succ k ih =>
    intro n t s U hk h
    cases n with
    | zero => omega
    | succ n =>
      have hp := ih n (t+1) (observeStep L t s U) U (by omega) h.2
      have ht : t+(k+1)=t+1+k := by omega
      simpa only [observeRun,ht] using hp

theorem source_observed_final (L : Rules H d T) (cap : ℝ) :
    ∀ n t (s : State H d T) (U : Frame d T), SourceObserved L cap n t s U →
      GenieProtocol.BoundedEnergy (finishObservation L (observeRun L n t s U)).2.1
        (observeRun L n t s U).2.2 U cap := by
  intro n
  induction n with
  | zero => intros; assumption
  | succ n ih => exact fun t s U h => ih (t+1) _ U h.2

end Bilevel.SourceFrameActions
