import NCConcave16991.OracleProgram

/-! # Correctness of state-loop oracle programs against direct state execution -/

namespace NCConcave16991.OracleProgram

variable {Q R X Ω State : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace State]

theorem loopState_snoc (initial : Ω → State) (update : ℕ → Ω → State → R → State)
    (seed : Ω) (t : ℕ) (replies : Fin t → R) (r : R) :
    loopState initial update (t + 1) seed (Fin.snoc replies r) =
      update t seed (loopState initial update t seed replies) r := by
  simp only [loopState, Fin.snoc_castSucc, Fin.snoc_last]

/-- Direct recursive state execution, supplied with an oracle only at interpretation time. -/
def executeStateFrom (ask : ℕ → Ω → State → Q) (update : ℕ → Ω → State → R → State)
    (oracle : Q → R) (seed : Ω) : ℕ → ℕ → State → State
  | 0, _, state => state
  | k + 1, t, state =>
      executeStateFrom ask update oracle seed k (t + 1)
        (update t seed state (oracle (ask t seed state)))

theorem evalFrom_stateLoop (T : ℕ) (initial : Ω → State) (hi : Measurable initial)
    (ask : ℕ → Ω → State → Q) (ha : ∀ t, Measurable (Function.uncurry (ask t)))
    (update : ℕ → Ω → State → R → State)
    (hu : ∀ t, Measurable (fun a : (Ω × State) × R => update t a.1.1 a.1.2 a.2))
    (finish : Ω → State → X) (hf : Measurable (Function.uncurry finish))
    (oracle : Q → R) (seed : Ω) (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) :
    evalFrom (stateLoop T initial hi ask ha update hu finish hf) oracle seed k t ht replies =
      finish seed (executeStateFrom ask update oracle seed k t
        (loopState initial update t seed replies)) := by
  induction k generalizing t with
  | zero =>
    have he : t = T := by omega
    subst t
    rfl
  | succ k ih =>
    change evalFrom (stateLoop T initial hi ask ha update hu finish hf) oracle seed k (t + 1) _
      (Fin.snoc replies (oracle (ask t seed (loopState initial update t seed replies)))) =
        finish seed (executeStateFrom ask update oracle seed k (t + 1)
          (update t seed (loopState initial update t seed replies)
            (oracle (ask t seed (loopState initial update t seed replies)))))
    rw [ih, loopState_snoc]

/-- A finite measurable state loop returns exactly the direct algorithm's final state output. -/
theorem eval_stateLoop (T : ℕ) (initial : Ω → State) (hi : Measurable initial)
    (ask : ℕ → Ω → State → Q) (ha : ∀ t, Measurable (Function.uncurry (ask t)))
    (update : ℕ → Ω → State → R → State)
    (hu : ∀ t, Measurable (fun a : (Ω × State) × R => update t a.1.1 a.1.2 a.2))
    (finish : Ω → State → X) (hf : Measurable (Function.uncurry finish))
    (oracle : Q → R) (seed : Ω) :
    eval (stateLoop T initial hi ask ha update hu finish hf) oracle seed =
      finish seed (executeStateFrom ask update oracle seed T 0 (initial seed)) :=
  evalFrom_stateLoop T initial hi ask ha update hu finish hf oracle seed T 0 (by omega) Fin.elim0

end NCConcave16991.OracleProgram
