import NCConcave16991.OracleProgramControl

/-! # The actual deterministic stateful interpreter for fixed oracle programs -/

namespace NCConcave16991.OracleProgram

variable {Q R X Y Ω Ω' S : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] [MeasurableSpace Ω'] {T U : ℕ}

def evalStateFrom (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (seed : Ω) :
    (k t : ℕ) → (ht : t + k = T) → (Fin t → R) → S → X × S
  | 0,t,ht,replies,state => (P.finish seed (fun i ↦ replies (Fin.cast ht.symm i)),state)
  | k + 1,t,ht,replies,state =>
      let a := oracle state (P.ask ⟨t,by omega⟩ seed replies)
      evalStateFrom P oracle seed k (t + 1) (by omega) (Fin.snoc replies a.2) a.1

def evalState (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (seed : Ω) (state : S) : X × S :=
  evalStateFrom P oracle seed T 0 (by omega) Fin.elim0 state

@[simp] theorem evalState_pure (f : Ω → X) (hf : Measurable f) (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    evalState (pure (Q := Q) (R := R) f hf) oracle seed state = (f seed,state) := rfl

@[simp] theorem evalState_query (q : Ω → Q) (hq : Measurable q) (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    evalState (query (R := R) q hq) oracle seed state = ((oracle state (q seed)).2,(oracle state (q seed)).1) := rfl

theorem evalStateFrom_map (P : Fixed Q R X Ω T) (f : X → Y) (hf : Measurable f)
    (oracle : S → Q → S × R) (seed : Ω) (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    evalStateFrom (map P f hf) oracle seed k t ht replies state =
      Prod.map f id (evalStateFrom P oracle seed k t ht replies state) := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _ _

theorem evalState_map (P : Fixed Q R X Ω T) (f : X → Y) (hf : Measurable f)
    (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    evalState (map P f hf) oracle seed state = Prod.map f id (evalState P oracle seed state) :=
  evalStateFrom_map P f hf oracle seed T 0 _ _ state

theorem evalStateFrom_withSeed (P : Fixed Q R X Ω T) (f : Ω' → Ω) (hf : Measurable f)
    (oracle : S → Q → S × R) (seed : Ω') (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    evalStateFrom (withSeed P f hf) oracle seed k t ht replies state =
      evalStateFrom P oracle (f seed) k t ht replies state := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _ _

theorem evalState_withSeed (P : Fixed Q R X Ω T) (f : Ω' → Ω) (hf : Measurable f)
    (oracle : S → Q → S × R) (seed : Ω') (state : S) :
    evalState (withSeed P f hf) oracle seed state = evalState P oracle (f seed) state :=
  evalStateFrom_withSeed P f hf oracle seed T 0 _ _ state

theorem evalStateFrom_mapWithSeed (P : Fixed Q R X Ω T) (f : Ω → X → Y)
    (hf : Measurable (Function.uncurry f)) (oracle : S → Q → S × R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    evalStateFrom (mapWithSeed P f hf) oracle seed k t ht replies state =
      Prod.map (f seed) id (evalStateFrom P oracle seed k t ht replies state) := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _ _

theorem evalState_mapWithSeed (P : Fixed Q R X Ω T) (f : Ω → X → Y)
    (hf : Measurable (Function.uncurry f)) (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    evalState (mapWithSeed P f hf) oracle seed state = Prod.map (f seed) id (evalState P oracle seed state) :=
  evalStateFrom_mapWithSeed P f hf oracle seed T 0 _ _ state

theorem evalState_castBudget (P : Fixed Q R X Ω T) (h : T = U)
    (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    evalState (castBudget P h) oracle seed state = evalState P oracle seed state := by
  subst U
  rfl

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]

theorem evalStateFrom_select (index : Ω → I) (hi : Measurable index) (program : I → Fixed Q R X Ω T)
    (oracle : S → Q → S × R) (seed : Ω) (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    evalStateFrom (select index hi program) oracle seed k t ht replies state =
      evalStateFrom (program (index seed)) oracle seed k t ht replies state := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _ _

theorem evalState_select (index : Ω → I) (hi : Measurable index) (program : I → Fixed Q R X Ω T)
    (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    evalState (select index hi program) oracle seed state = evalState (program (index seed)) oracle seed state :=
  evalStateFrom_select index hi program oracle seed T 0 _ _ state

end NCConcave16991.OracleProgram
