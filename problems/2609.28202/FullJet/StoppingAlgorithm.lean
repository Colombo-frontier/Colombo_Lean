import FullJet.AlgorithmModel
import Mathlib.Probability.Process.Stopping

open MeasureTheory

namespace FullJet

/-- A stopping rule is evaluated from the private seed and current oracle
state. It is not given the component functions or their future replies. -/
structure StoppingJetAlgorithm (Ω E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (n p : ℕ) where
  core : JetAlgorithm Ω E n p
  halt : Ω → core.State → Bool

namespace StoppingJetAlgorithm

variable {Ω E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n p : ℕ}

/-- A fixed-budget execution freezes its state once the stopping test passes.
Padding calls count toward the cap but cannot change the stopped output. -/
def capped (A : StoppingJetAlgorithm Ω E n p) : JetAlgorithm Ω E n p :=
  { A.core with update := fun s state reply =>
      if (A.halt s state) then state else A.core.update s state reply }

noncomputable def state (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ)
    (s : Ω) (N : ℕ) : A.core.State :=
  oracleRun (A.capped.query s) (A.capped.update s) (fun q => fullJet p (f q.1) q.2) (A.core.initial s) N

def Halts (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ) (s : Ω) : Prop :=
  ∃ N, A.halt s (A.state f s N) = true

/-- On nonterminating seeds this auxiliary natural index is zero; termination
is recorded separately, and the genuine stopping time below is infinity. -/
noncomputable def stopIndex (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ) (s : Ω) : ℕ := by
  classical
  exact if h : A.Halts f s then Nat.find h else 0

noncomputable def stopTime (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ)
    (s : Ω) : WithTop ℕ := by
  classical
  exact if A.Halts f s then (A.stopIndex f s : WithTop ℕ) else ⊤

noncomputable def stoppedResult (A : StoppingJetAlgorithm Ω E n p)
    (f : Fin n → E → ℝ) (s : Ω) : E := A.core.output s (A.state f s (A.stopIndex f s))

theorem state_succ (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ) (s : Ω) (N : ℕ) :
    A.state f s (N + 1) =
      if A.halt s (A.state f s N) then A.state f s N
      else A.core.update s (A.state f s N)
        (fullJet p (f (A.core.query s (A.state f s N)).1) (A.core.query s (A.state f s N)).2) := rfl

theorem state_after_halt (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ)
    (s : Ω) {N M : ℕ} (hhalt : A.halt s (A.state f s N) = true) (hNM : N ≤ M) :
    A.state f s M = A.state f s N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  clear hNM
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Nat.add_succ, state_succ, ih]
    simp only [hhalt, Bool.true_eq, if_true]

theorem stopIndex_spec (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ)
    (s : Ω) (h : A.Halts f s) : A.halt s (A.state f s (A.stopIndex f s)) = true := by
  classical
  rw [stopIndex, dif_pos h]
  exact Nat.find_spec h

theorem stopIndex_le_of_halt (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ)
    (s : Ω) {N : ℕ} (h : A.halt s (A.state f s N) = true) : A.stopIndex f s ≤ N := by
  classical
  have hh : A.Halts f s := ⟨N, h⟩
  rw [stopIndex, dif_pos hh]
  exact Nat.find_min' hh h

theorem halt_of_stopIndex_le (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ)
    (s : Ω) (h : A.Halts f s) {N : ℕ} (hN : A.stopIndex f s ≤ N) :
    A.halt s (A.state f s N) = true := by
  rw [A.state_after_halt f s (A.stopIndex_spec f s h) hN]
  exact A.stopIndex_spec f s h

/-- Stopping by time N is decided by the actual state after N replies. -/
theorem stopTime_le_iff (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ)
    (s : Ω) (N : ℕ) : A.stopTime f s ≤ (N : WithTop ℕ) ↔ A.halt s (A.state f s N) = true := by
  classical
  by_cases h : A.Halts f s
  · simp only [stopTime, if_pos h]
    constructor
    · intro hN
      apply A.halt_of_stopIndex_le f s h
      exact_mod_cast hN
    · intro hh
      exact_mod_cast A.stopIndex_le_of_halt f s hh
  · have hh : ¬ A.halt s (A.state f s N) = true := fun hh => h ⟨N, hh⟩
    simp [stopTime, h, hh]

theorem stopTime_eq_top_iff (A : StoppingJetAlgorithm Ω E n p) (f : Fin n → E → ℝ) (s : Ω) :
    A.stopTime f s = ⊤ ↔ ¬ A.Halts f s := by
  classical
  by_cases h : A.Halts f s <;> simp [stopTime, h]

theorem capped_result_eq_stoppedResult (A : StoppingJetAlgorithm Ω E n p)
    (f : Fin n → E → ℝ) (s : Ω) (h : A.Halts f s) {N : ℕ} (hN : A.stopIndex f s ≤ N) :
    A.capped.result N f s = A.stoppedResult f s := by
  change A.core.output s (A.state f s N) = A.core.output s (A.state f s (A.stopIndex f s))
  rw [A.state_after_halt f s (A.stopIndex_spec f s h) hN]

/-- For any filtration making the actual halt tests observable at their
query times, the derived first halt is a stopping time, including infinity. -/
theorem isStoppingTime [MeasurableSpace Ω] (A : StoppingJetAlgorithm Ω E n p)
    (f : Fin n → E → ℝ) (𝓕 : Filtration (WithTop ℕ) (inferInstance : MeasurableSpace Ω))
    (hobs : ∀ N : ℕ, MeasurableSet[𝓕 N] {s | A.halt s (A.state f s N) = true}) :
    IsStoppingTime 𝓕 (A.stopTime f) := by
  intro t
  induction t using WithTop.recTopCoe with
  | top => simpa only [le_top, Set.setOf_true] using (@MeasurableSet.univ Ω (𝓕 ⊤))
  | coe N =>
    change MeasurableSet[𝓕 (N : WithTop ℕ)] {s | A.stopTime f s ≤ (N : WithTop ℕ)}
    simpa only [A.stopTime_le_iff f] using hobs N

end StoppingJetAlgorithm

def UniformStoppingAlgorithm (Ω : Type) (n p : ℕ) :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    StoppingJetAlgorithm Ω E n p

end FullJet
