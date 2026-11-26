import NCConcave16991.OracleProgramBind
import NCConcave16991.OracleProgramTransform

/-! # Finite state loops with public, stage-dependent query counts -/

namespace NCConcave16991.OracleProgram

variable {Q R Ω State : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace Ω] [MeasurableSpace State]

def foldBudget (cost : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, t => cost t + foldBudget cost k (t + 1)

/-- Each stage may have a different public cost; the new state is passed only as a reply-derived value. -/
def fold (cost : ℕ → ℕ) (step : ∀ t, Fixed Q R State (Ω × State) (cost t)) :
    (k t : ℕ) → Fixed Q R State (Ω × State) (foldBudget cost k t)
  | 0, _ => pure Prod.snd measurable_snd
  | k + 1, t => bind (step t)
      (withSeed (fold cost step k (t + 1))
        (fun a : (Ω × State) × State => (a.1.1, a.2))
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

def executeBlocks (step : ℕ → State → State) : ℕ → ℕ → State → State
  | 0, _, state => state
  | k + 1, t, state => executeBlocks step k (t + 1) (step t state)

/-- Sequential program composition agrees exactly with direct stage-by-stage execution. -/
theorem eval_fold (cost : ℕ → ℕ) (step : ∀ t, Fixed Q R State (Ω × State) (cost t))
    (oracle : Q → R) (seed : Ω) (state : State) (k t : ℕ) :
    eval (fold cost step k t) oracle (seed, state) =
      executeBlocks (fun j s => eval (step j) oracle (seed, s)) k t state := by
  induction k generalizing state t with
  | zero => rfl
  | succ k ih =>
    change eval (bind (step t)
      (withSeed (fold cost step k (t + 1))
        (fun a : (Ω × State) × State => (a.1.1, a.2))
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))) oracle (seed, state) = _
    rw [eval_bind, eval_withSeed, ih]
    rfl

theorem foldBudget_constant (c k t : ℕ) : foldBudget (fun _ => c) k t = k * c := by
  induction k generalizing t with
  | zero => simp [foldBudget]
  | succ k ih => simp only [foldBudget, ih, Nat.succ_mul, Nat.add_comm]

end NCConcave16991.OracleProgram
