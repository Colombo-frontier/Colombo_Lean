import NCConcave16991.DenseSmoothRevelationAccounting
import NCConcave16991.DenseSmoothMachineFresh

/-! # The alignment-free current-stage machine consumes only fresh rows -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open Set MeasureTheory

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

def CurrentCorrect (A : Table E n T ρ) (s : State E n T hn ρ hρ) : Prop :=
  Machine.CurrentCorrect E n T hn ρ hρ A s.base

def effectiveAnswer (seed : Ω) (s : State E n T hn ρ hρ) (a : E) : E :=
  Machine.effectiveAnswer E n T hn ρ hρ P seed s.base a

def censoredRequest (seed : Ω) (s : State E n T hn ρ hρ) : Option (Fin n) :=
  (freshRequest E n T hn ρ hρ P seed s).map Prod.snd

def censoredAdvance (seed : Ω) (s : State E n T hn ρ hρ) (a : E) : State E n T hn ρ hρ :=
  precompletionStep E n T hn ρ hρ P seed s (effectiveAnswer E n T hn ρ hρ P seed s a)

theorem precompletionStep_seen (seed : Ω) (s : State E n T hn ρ hρ) (a : E) :
    (precompletionStep E n T hn ρ hρ P seed s a).base.progress.2 =
      (request E n T hn ρ hρ P seed s).elim s.base.progress.2 (fun ji ↦ insert ji.2 s.base.progress.2) := by
  unfold precompletionStep step request
  cases action E n T hn ρ hρ P seed s with
  | inl x => rfl
  | inr o =>
      simp only [Sum.elim_inr]
      by_cases hf : frontier E n T hn ρ hρ s < T + 1 <;>
        simp only [paidQuery, hf, ite_true, ite_false, Bool.false_eq_true, Option.elim_some, Option.elim_none]

theorem censoredAdvance_seen (seed : Ω) (s : State E n T hn ρ hρ) (a : E) :
    (censoredAdvance E n T hn ρ hρ P seed s a).base.progress.2 =
      (censoredRequest E n T hn ρ hρ P seed s).elim s.base.progress.2 (fun i ↦ insert i s.base.progress.2) := by
  rw [censoredAdvance, precompletionStep_seen]
  cases hr : request E n T hn ρ hρ P seed s with
  | none => simp [censoredRequest, freshRequest, hr]
  | some ji =>
      by_cases hi : ji.2 ∈ s.base.progress.2
      · simp [censoredRequest, freshRequest, hr, hi, Option.filter, Finset.insert_eq_of_mem hi]
      · simp [censoredRequest, freshRequest, hr, hi, Option.filter]

theorem censoredRequest_fresh (seed : Ω) (s : State E n T hn ρ hρ) (i : Fin n)
    (hi : censoredRequest E n T hn ρ hρ P seed s = some i) : i ∉ s.base.progress.2 := by
  cases hr : request E n T hn ρ hρ P seed s with
  | none => simp [censoredRequest, freshRequest, hr] at hi
  | some ji =>
      by_cases hj : ji.2 ∈ s.base.progress.2
      · simp [censoredRequest, freshRequest, hr, hj, Option.filter] at hi
      · have he : ji.2 = i := by simpa [censoredRequest, freshRequest, hr, hj, Option.filter] using hi
        exact he ▸ hj

theorem request_eq_machine (seed : Ω) (s : State E n T hn ρ hρ) :
    request E n T hn ρ hρ P seed s = Machine.request E n T hn ρ hρ P seed s.base := rfl

theorem freshRequest_eq_machine (seed : Ω) (s : State E n T hn ρ hρ) :
    freshRequest E n T hn ρ hρ P seed s = Machine.freshRequest E n T hn ρ hρ P seed s.base := rfl

theorem precompletionStep_base_eq_machine (seed : Ω) (s : State E n T hn ρ hρ)
    (a : E) (releasedRows : Fin n → E) :
    (precompletionStep E n T hn ρ hρ P seed s a).base =
      Machine.step E n T hn ρ hρ P seed (n + 1) s.base a releasedRows := by
  unfold precompletionStep step action Machine.step
  cases ha : OracleSimulation.action (Domain n T hn ρ hρ) P seed s.base.control with
  | inl x => rfl
  | inr o =>
      simp only [Sum.elim_inr]
      have hcard : (insert o.1 s.base.progress.2).card ≤ n := by simpa using Finset.card_le_univ (insert o.1 s.base.progress.2)
      have hrel : ¬ n + 1 ≤ (insert o.1 s.base.progress.2).card := by omega
      by_cases hf : frontier E n T hn ρ hρ s < T + 1
      · have hf' : s.base.progress.1 < T + 1 := hf
        simp only [paidQuery, hf, ite_true, Bool.false_eq_true, ite_false, Machine.paidQuery,
          hf', Machine.shouldRelease, hrel, decide_false, Counter.step]
        rfl
      · have hf' : ¬ s.base.progress.1 < T + 1 := hf
        simp only [paidQuery, hf, ite_false, Machine.paidQuery, hf']

theorem precompletionStep_currentCorrect (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (hs : CurrentCorrect E n T hn ρ hρ A s) :
    CurrentCorrect E n T hn ρ hρ A (precompletionStep E n T hn ρ hρ P seed s
      ((request E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1))) := by
  unfold CurrentCorrect
  rw [precompletionStep_base_eq_machine]
  change Machine.CurrentCorrect E n T hn ρ hρ A
    (Machine.stepWithRows E n T hn ρ hρ P seed (n + 1) (fun j i ↦ A.row i j) s.base)
  exact Machine.stepWithRows_currentCorrect E n T hn ρ hρ P seed (n + 1) A s.base hs

theorem precompletionStep_eq_fresh (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (hs : CurrentCorrect E n T hn ρ hρ A s) :
    precompletionStep E n T hn ρ hρ P seed s
      ((request E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1)) =
      censoredAdvance E n T hn ρ hρ P seed s
        ((freshRequest E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1)) := by
  have he := Machine.effectiveAnswer_correct E n T hn ρ hρ P seed A s.base hs
  change effectiveAnswer E n T hn ρ hρ P seed s
    ((freshRequest E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1)) =
      (request E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1) at he
  rw [censoredAdvance, he]

theorem stepWithTable_eq_fresh_censor (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (hs : CurrentCorrect E n T hn ρ hρ A s) (hc : completion E n T hn ρ hρ P seed A s = false) :
    stepWithTable E n T hn ρ hρ P seed A s = censoredAdvance E n T hn ρ hρ P seed s
      ((freshRequest E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1)) := by
  rw [stepWithTable_noncompletion E n T hn ρ hρ P seed A s hc,
    precompletionStep_eq_fresh E n T hn ρ hρ P seed A s hs]

end

end NCConcave16991.DenseSmooth.Revelation
