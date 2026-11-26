import NCConcave16991.OracleProgramState
import NCConcave16991.OracleProgramLibrary

/-! # Actual full-pass state execution and per-query support contracts -/

namespace NCConcave16991.OracleProgram

variable {Q R X Ω S : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Ω] {T : ℕ}

def executeBatchFrom (queries : Fin T → Q) (oracle : S → Q → S × R) :
    (k t : ℕ) → (ht : t + k = T) → (Fin t → R) → S → (Fin T → R) × S
  | 0,t,ht,replies,state => (fun i ↦ replies (Fin.cast ht.symm i),state)
  | k + 1,t,ht,replies,state =>
      let a := oracle state (queries ⟨t,by omega⟩)
      executeBatchFrom queries oracle k (t + 1) (by omega) (Fin.snoc replies a.2) a.1

def executeBatch (queries : Fin T → Q) (oracle : S → Q → S × R) (state : S) : (Fin T → R) × S :=
  executeBatchFrom queries oracle T 0 (by omega) Fin.elim0 state

theorem evalStateFrom_fullPass (queries : Ω → Fin T → Q)
    (hq : ∀ i, Measurable (fun seed ↦ queries seed i)) (oracle : S → Q → S × R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    evalStateFrom (fullPass (R := R) queries hq) oracle seed k t ht replies state =
      executeBatchFrom (queries seed) oracle k t ht replies state := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _ _

theorem evalState_fullPass (queries : Ω → Fin T → Q)
    (hq : ∀ i, Measurable (fun seed ↦ queries seed i)) (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    evalState (fullPass (R := R) queries hq) oracle seed state = executeBatch (queries seed) oracle state :=
  evalStateFrom_fullPass queries hq oracle seed T 0 _ _ state

theorem evalStateFrom_spec (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (seed : Ω)
    (Inv : ∀ t : ℕ, (Fin t → R) → S → Prop) (Post : X → S → Prop)
    (hfinish : ∀ replies state, Inv T replies state → Post (P.finish seed replies) state)
    (hstep : ∀ (t : ℕ) (ht : t < T) (replies : Fin t → R) (state : S), Inv t replies state →
      let a := oracle state (P.ask ⟨t,ht⟩ seed replies)
      Inv (t + 1) (Fin.snoc replies a.2) a.1)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) (hinv : Inv t replies state) :
    Post (evalStateFrom P oracle seed k t ht replies state).1
      (evalStateFrom P oracle seed k t ht replies state).2 := by
  induction k generalizing t state with
  | zero =>
      have he : t = T := by omega
      subst t
      simpa only [evalStateFrom,Fin.cast_refl,Function.id_def] using hfinish replies state hinv
  | succ k ih =>
      exact ih (t + 1) (by omega) _ _ (hstep t (by omega) replies state hinv)

theorem evalState_spec (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (seed : Ω)
    (Inv : ∀ t : ℕ, (Fin t → R) → S → Prop) (Post : X → S → Prop)
    (hfinish : ∀ replies state, Inv T replies state → Post (P.finish seed replies) state)
    (hstep : ∀ (t : ℕ) (ht : t < T) (replies : Fin t → R) (state : S), Inv t replies state →
      let a := oracle state (P.ask ⟨t,ht⟩ seed replies)
      Inv (t + 1) (Fin.snoc replies a.2) a.1)
    (state : S) (hinv : Inv 0 Fin.elim0 state) :
    Post (evalState P oracle seed state).1 (evalState P oracle seed state).2 :=
  evalStateFrom_spec P oracle seed Inv Post hfinish hstep T 0 (by omega) Fin.elim0 state hinv

theorem evalState_fullPass_spec (queries : Ω → Fin T → Q)
    (hq : ∀ i, Measurable (fun seed ↦ queries seed i)) (oracle : S → Q → S × R) (seed : Ω)
    (Inv : S → Prop) (ReplyGood : Fin T → R → Prop)
    (hstep : ∀ (i : Fin T) (state : S), Inv state →
      Inv (oracle state (queries seed i)).1 ∧ ReplyGood i (oracle state (queries seed i)).2)
    (state : S) (hinv : Inv state) :
    Inv (evalState (fullPass (R := R) queries hq) oracle seed state).2 ∧
      ∀ i : Fin T, ReplyGood i ((evalState (fullPass (R := R) queries hq) oracle seed state).1 i) := by
  let I : ∀ t : ℕ, (Fin t → R) → S → Prop := fun t replies state ↦
    Inv state ∧ ∀ i : Fin t, ∀ hi : i.val < T, ReplyGood ⟨i.val,hi⟩ (replies i)
  refine evalState_spec (fullPass queries hq) oracle seed I
    (fun replies state ↦ Inv state ∧ ∀ i, ReplyGood i (replies i)) ?_ ?_ state ?_
  · intro replies state hs
    exact ⟨hs.1,fun i ↦ hs.2 i i.isLt⟩
  · intro t ht replies state hs
    have ha := hstep ⟨t,ht⟩ state hs.1
    refine ⟨ha.1,?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · intro hi
      simpa only [Fin.snoc_last,Fin.val_last,fullPass] using ha.2
    · intro hi
      simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hs.2 j (by omega)
  · exact ⟨hinv,fun i ↦ Fin.elim0 i⟩

end NCConcave16991.OracleProgram
