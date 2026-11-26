import Mathlib.Data.Nat.Basic

/-!
# Program-level coupling of adaptive oracle transcripts

A deterministic state may contain the complete query history and a fixed
private random seed. The two runs use the same query/update/halting/output
functions and the same sequence of activation bits. Their oracle responses
need coincide only on inactive calls. The theorem proves equality of stopped
outputs before any activation, rather than assuming it as a testing premise.

This is a program-level theorem. Measurability and a probability law on seeds
and fresh bits remain separate from the state-machine construction here.
-/

namespace Bilevel.Transcript

variable {State Query Observation Output : Type*}

/-- Unhalted recursion through oracle calls. A stopped execution reads this
sequence only up to its first halt. -/
def run (query : State → Query) (update : State → Observation → State)
    (oracle : Query → Bool → Observation) (draws : ℕ → Bool) (initial : State) : ℕ → State
  | 0 => initial
  | n + 1 =>
    let state := run query update oracle draws initial n
    update state (oracle (query state) (draws n))

/-- The two actual adaptive states coincide up to any all-inactive prefix. -/
theorem run_eq_of_inactive
    (query : State → Query) (update : State → Observation → State)
    (oraclePlus oracleMinus : Query → Bool → Observation)
    (inactive : ∀ q, oraclePlus q false = oracleMinus q false)
    (draws : ℕ → Bool) (initial : State) (n : ℕ)
    (no_activation : ∀ t < n, draws t = false) :
    run query update oraclePlus draws initial n =
      run query update oracleMinus draws initial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprefix : ∀ t < n, draws t = false := by
      intro t ht
      exact no_activation t (Nat.lt_trans ht (Nat.lt_succ_self n))
    simp only [run, ih hprefix, no_activation n (Nat.lt_succ_self n), inactive]

/-- A first halting index, including the possible zero-query index. -/
def FirstHalt (halt : State → Bool) (states : ℕ → State) (n : ℕ) : Prop :=
  halt (states n) = true ∧ ∀ t < n, halt (states t) = false

/-- Any two first halting indices of the same state sequence agree. -/
theorem firstHalt_unique (halt : State → Bool) (states : ℕ → State)
    {n m : ℕ} (hn : FirstHalt halt states n) (hm : FirstHalt halt states m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · have hf := hm.2 n h
    rw [hn.1] at hf
    contradiction
  · exact h
  · have hf := hn.2 m h
    rw [hm.1] at hf
    contradiction

/-- If the plus run stops before the first activation, its stopping index is
also the minus run's first halting index. This proves existence for that run. -/
theorem firstHalt_transfer
    (query : State → Query) (update : State → Observation → State)
    (oraclePlus oracleMinus : Query → Bool → Observation)
    (inactive : ∀ q, oraclePlus q false = oracleMinus q false)
    (draws : ℕ → Bool) (initial : State) (halt : State → Bool) {n : ℕ}
    (hplus : FirstHalt halt (run query update oraclePlus draws initial) n)
    (no_activation : ∀ t < n, draws t = false) :
    FirstHalt halt (run query update oracleMinus draws initial) n := by
  constructor
  · rw [← run_eq_of_inactive query update oraclePlus oracleMinus inactive draws initial n
      no_activation]
    exact hplus.1
  · intro t ht
    rw [← run_eq_of_inactive query update oraclePlus oracleMinus inactive draws initial t
      (fun s hs => no_activation s (Nat.lt_trans hs ht))]
    exact hplus.2 t ht

/-- Before activation, actual first stopping times and terminal outputs agree. -/
theorem stopped_outputs_equal
    (query : State → Query) (update : State → Observation → State)
    (oraclePlus oracleMinus : Query → Bool → Observation)
    (inactive : ∀ q, oraclePlus q false = oracleMinus q false)
    (draws : ℕ → Bool) (initial : State) (halt : State → Bool) (output : State → Output)
    {nPlus nMinus : ℕ}
    (hplus : FirstHalt halt (run query update oraclePlus draws initial) nPlus)
    (hminus : FirstHalt halt (run query update oracleMinus draws initial) nMinus)
    (no_activation : ∀ t < nPlus, draws t = false) :
    nPlus = nMinus ∧
      output (run query update oraclePlus draws initial nPlus) =
        output (run query update oracleMinus draws initial nMinus) := by
  have hm := firstHalt_transfer query update oraclePlus oracleMinus inactive draws initial
    halt hplus no_activation
  have hn : nPlus = nMinus := firstHalt_unique halt _ hm hminus
  refine ⟨hn, ?_⟩
  rw [← hn, run_eq_of_inactive query update oraclePlus oracleMinus inactive draws initial nPlus
    no_activation]

/-- The all-inactive-before-stopping property is the same for both coupled
runs, even though their stopping indices can differ after an activation. -/
theorem no_activation_iff
    (query : State → Query) (update : State → Observation → State)
    (oraclePlus oracleMinus : Query → Bool → Observation)
    (inactive : ∀ q, oraclePlus q false = oracleMinus q false)
    (draws : ℕ → Bool) (initial : State) (halt : State → Bool)
    {nPlus nMinus : ℕ}
    (hplus : FirstHalt halt (run query update oraclePlus draws initial) nPlus)
    (hminus : FirstHalt halt (run query update oracleMinus draws initial) nMinus) :
    (∀ t < nPlus, draws t = false) ↔ (∀ t < nMinus, draws t = false) := by
  constructor
  · intro h
    have hn := firstHalt_unique halt _
      (firstHalt_transfer query update oraclePlus oracleMinus inactive draws initial halt hplus h)
      hminus
    simpa only [← hn] using h
  · intro h
    have hn := firstHalt_unique halt _
      (firstHalt_transfer query update oracleMinus oraclePlus (fun q => (inactive q).symm)
        draws initial halt hminus h) hplus
    simpa only [← hn] using h

end Bilevel.Transcript
