import NCConcave16991.OracleProgramStateBind
import NCConcave16991.OracleProgramFold

/-! # Stateful execution of the literal public finite block fold -/

namespace NCConcave16991.OracleProgram

variable {Q R Ω B S : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace Ω] [MeasurableSpace B]

def executeStateBlocks (step : ℕ → B → S → B × S) : ℕ → ℕ → B → S → B × S
  | 0,_,value,state => (value,state)
  | k + 1,t,value,state =>
      let a := step t value state
      executeStateBlocks step k (t + 1) a.1 a.2

theorem evalState_fold (cost : ℕ → ℕ) (step : ∀ t, Fixed Q R B (Ω × B) (cost t))
    (oracle : S → Q → S × R) (seed : Ω) (value : B) (state : S) (k t : ℕ) :
    evalState (fold cost step k t) oracle (seed,value) state =
      executeStateBlocks (fun j value state ↦ evalState (step j) oracle (seed,value) state) k t value state := by
  induction k generalizing value state t with
  | zero => rfl
  | succ k ih =>
      change evalState (bind (step t)
        (withSeed (fold cost step k (t + 1))
          (fun a : (Ω × B) × B ↦ (a.1.1,a.2))
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))) oracle (seed,value) state = _
      rw [evalState_bind]
      simp only [evalState_withSeed,ih]
      rfl

theorem executeStateBlocks_invariant (step : ℕ → B → S → B × S) (Inv : ℕ → B → S → Prop)
    (hstep : ∀ t value state, Inv t value state → Inv (t + 1) (step t value state).1 (step t value state).2)
    (k t : ℕ) (value : B) (state : S) (hinv : Inv t value state) :
    Inv (t + k) (executeStateBlocks step k t value state).1 (executeStateBlocks step k t value state).2 := by
  induction k generalizing t value state with
  | zero => exact hinv
  | succ k ih =>
      have hh := ih (t + 1) _ _ (hstep t value state hinv)
      simpa only [executeStateBlocks,Nat.add_assoc,Nat.add_comm 1 k] using hh

theorem evalState_fold_invariant (cost : ℕ → ℕ) (step : ∀ t, Fixed Q R B (Ω × B) (cost t))
    (oracle : S → Q → S × R) (seed : Ω) (Inv : ℕ → B → S → Prop)
    (hstep : ∀ t value state, Inv t value state →
      Inv (t + 1) (evalState (step t) oracle (seed,value) state).1
        (evalState (step t) oracle (seed,value) state).2)
    (k t : ℕ) (value : B) (state : S) (hinv : Inv t value state) :
    Inv (t + k) (evalState (fold cost step k t) oracle (seed,value) state).1
      (evalState (fold cost step k t) oracle (seed,value) state).2 := by
  rw [evalState_fold]
  exact executeStateBlocks_invariant _ Inv hstep k t value state hinv

end NCConcave16991.OracleProgram
