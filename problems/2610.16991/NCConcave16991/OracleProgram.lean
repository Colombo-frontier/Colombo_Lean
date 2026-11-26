import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Lean.Elab.Tactic.Omega

/-!
# Finite interactive oracle programs

A program has a public exact query count. Each query is a measurable function
of its private seed and the previously supplied oracle replies. The unknown
oracle is supplied only to the interpreter, never to the program constructor.
-/

namespace NCConcave16991.OracleProgram

variable {Q R X Y Ω : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]

/-- An intrinsically measurable program with exactly T interactive oracle queries. -/
structure Fixed (Q R X Ω : Type*) [MeasurableSpace Q] [MeasurableSpace R]
    [MeasurableSpace X] [MeasurableSpace Ω] (T : ℕ) where
  ask : (t : Fin T) → Ω → (Fin t.val → R) → Q
  finish : Ω → (Fin T → R) → X
  ask_measurable : ∀ t, Measurable (Function.uncurry (ask t))
  finish_measurable : Measurable (Function.uncurry finish)

variable {T U : ℕ}

/-- Return without querying the oracle. -/
def pure (f : Ω → X) (hf : Measurable f) : Fixed Q R X Ω 0 where
  ask t := Fin.elim0 t
  finish seed _ := f seed
  ask_measurable t := Fin.elim0 t
  finish_measurable := hf.comp measurable_fst

/-- One query, returning its supplied reply. -/
def query (q : Ω → Q) (hq : Measurable q) : Fixed Q R R Ω 1 where
  ask _ seed _ := q seed
  finish _ replies := replies 0
  ask_measurable _ := hq.comp measurable_fst
  finish_measurable := (measurable_pi_apply 0).comp measurable_snd

/-- Measurable postprocessing does not consume queries. -/
def map (P : Fixed Q R X Ω T) (f : X → Y) (hf : Measurable f) : Fixed Q R Y Ω T where
  ask := P.ask
  finish seed replies := f (P.finish seed replies)
  ask_measurable := P.ask_measurable
  finish_measurable := hf.comp P.finish_measurable

theorem measurable_reindex {a b : ℕ} (f : Fin a → Fin b) :
    Measurable (fun replies : Fin b → R => fun i => replies (f i)) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply (f i)

/-- Sequential composition: Q sees the private seed and the actual result of P. -/
def bind (P : Fixed Q R X Ω T) (N : Fixed Q R Y (Ω × X) U) : Fixed Q R Y Ω (T + U) where
  ask t seed replies := if ht : t.val < T then
      P.ask ⟨t.val, ht⟩ seed replies
    else
      N.ask ⟨t.val - T, by omega⟩
        (seed, P.finish seed (fun i => replies ⟨i.val, by omega⟩))
        (fun i => replies ⟨T + i.val, by have hi : i.val < t.val - T := i.isLt; omega⟩)
  finish seed replies :=
    N.finish (seed, P.finish seed (fun i => replies ⟨i.val, by omega⟩))
      (fun i => replies ⟨T + i.val, by omega⟩)
  ask_measurable t := by
    dsimp only
    split_ifs with ht
    · exact P.ask_measurable ⟨t.val, ht⟩
    · change Measurable (Function.uncurry (N.ask ⟨t.val - T, by omega⟩) ∘
        (fun a : Ω × (Fin t.val → R) =>
          ((a.1, P.finish a.1 (fun i => a.2 ⟨i.val, by omega⟩)),
            fun i : Fin (t.val - T) => a.2 ⟨T + i.val, by omega⟩)))
      apply (N.ask_measurable ⟨t.val - T, by omega⟩).comp
      apply Measurable.prodMk
      · apply Measurable.prodMk measurable_fst
        exact P.finish_measurable.comp
          (measurable_fst.prodMk ((measurable_reindex _).comp measurable_snd))
      · exact (measurable_reindex _).comp measurable_snd
  finish_measurable := by
    change Measurable (Function.uncurry N.finish ∘ (fun a : Ω × (Fin (T + U) → R) =>
      ((a.1, P.finish a.1 (fun i => a.2 ⟨i.val, by omega⟩)),
        fun i => a.2 ⟨T + i.val, by omega⟩)))
    apply N.finish_measurable.comp
    apply Measurable.prodMk
    · apply Measurable.prodMk measurable_fst
      exact P.finish_measurable.comp
        (measurable_fst.prodMk ((measurable_reindex _).comp measurable_snd))
    · exact (measurable_reindex _).comp measurable_snd

/-- The independent interpreter consumes only replies to the queries it issues. -/
def evalFrom (P : Fixed Q R X Ω T) (oracle : Q → R) (seed : Ω) :
    (k t : ℕ) → (ht : t + k = T) → (Fin t → R) → X
  | 0, t, ht, replies => P.finish seed (fun i => replies (Fin.cast ht.symm i))
  | k + 1, t, ht, replies =>
      let q := P.ask ⟨t, by omega⟩ seed replies
      evalFrom P oracle seed k (t + 1) (by omega) (Fin.snoc replies (oracle q))

def eval (P : Fixed Q R X Ω T) (oracle : Q → R) (seed : Ω) : X :=
  evalFrom P oracle seed T 0 (by omega) Fin.elim0

@[simp] theorem eval_pure (f : Ω → X) (hf : Measurable f) (oracle : Q → R) (seed : Ω) :
    eval (pure (Q := Q) (R := R) f hf) oracle seed = f seed := rfl

@[simp] theorem eval_query (q : Ω → Q) (hq : Measurable q) (oracle : Q → R) (seed : Ω) :
    eval (query (R := R) q hq) oracle seed = oracle (q seed) := rfl

theorem evalFrom_map (P : Fixed Q R X Ω T) (f : X → Y) (hf : Measurable f)
    (oracle : Q → R) (seed : Ω) (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) :
    evalFrom (map P f hf) oracle seed k t ht replies =
      f (evalFrom P oracle seed k t ht replies) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _

theorem eval_map (P : Fixed Q R X Ω T) (f : X → Y) (hf : Measurable f)
    (oracle : Q → R) (seed : Ω) :
    eval (map P f hf) oracle seed = f (eval P oracle seed) :=
  evalFrom_map P f hf oracle seed T 0 _ _

section StateLoop

variable {State : Type*} [MeasurableSpace State]

/-- Internal state is reconstructed from the public initial state and supplied reply prefix. -/
def loopState (initial : Ω → State) (update : ℕ → Ω → State → R → State) :
    (t : ℕ) → Ω → (Fin t → R) → State
  | 0, seed, _ => initial seed
  | t + 1, seed, replies => update t seed
      (loopState initial update t seed (fun i => replies i.castSucc)) (replies (Fin.last t))

theorem loopState_measurable (initial : Ω → State) (hi : Measurable initial)
    (update : ℕ → Ω → State → R → State)
    (hu : ∀ t, Measurable (fun a : (Ω × State) × R => update t a.1.1 a.1.2 a.2))
    (t : ℕ) : Measurable (Function.uncurry (loopState initial update t)) := by
  induction t with
  | zero => exact hi.comp measurable_fst
  | succ t ih =>
    change Measurable ((fun a : (Ω × State) × R => update t a.1.1 a.1.2 a.2) ∘
      (fun a : Ω × (Fin (t + 1) → R) =>
        ((a.1, loopState initial update t a.1 (fun i => a.2 i.castSucc)), a.2 (Fin.last t))))
    apply (hu t).comp
    apply Measurable.prodMk
    · exact measurable_fst.prodMk
        (ih.comp (measurable_fst.prodMk ((measurable_reindex Fin.castSucc).comp measurable_snd)))
    · exact (measurable_pi_apply (Fin.last t)).comp measurable_snd

/-- Finite state loops compile into measurable fixed-query programs. -/
def stateLoop (T : ℕ) (initial : Ω → State) (hi : Measurable initial)
    (ask : ℕ → Ω → State → Q)
    (ha : ∀ t, Measurable (Function.uncurry (ask t)))
    (update : ℕ → Ω → State → R → State)
    (hu : ∀ t, Measurable (fun a : (Ω × State) × R => update t a.1.1 a.1.2 a.2))
    (finish : Ω → State → X) (hf : Measurable (Function.uncurry finish)) :
    Fixed Q R X Ω T where
  ask t seed replies := ask t seed (loopState initial update t seed replies)
  finish seed replies := finish seed (loopState initial update T seed replies)
  ask_measurable t := (ha t).comp (measurable_fst.prodMk (loopState_measurable initial hi update hu t))
  finish_measurable := hf.comp (measurable_fst.prodMk (loopState_measurable initial hi update hu T))

end StateLoop

end NCConcave16991.OracleProgram
