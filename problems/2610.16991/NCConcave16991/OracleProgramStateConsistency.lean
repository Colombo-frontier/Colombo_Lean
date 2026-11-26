import NCConcave16991.OracleProgramState
import NCConcave16991.OracleProgramRecord

/-! # A fixed latent oracle agrees with the actual stateful query chronology -/

namespace NCConcave16991.OracleProgram

variable {Q R X Ω S : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Ω] {T : ℕ}

def ConsistentFrom (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (A : Q → R) (seed : Ω) :
    (k t : ℕ) → (ht : t + k = T) → (Fin t → R) → S → Prop
  | 0,_,_,_,_ => True
  | k + 1,t,ht,replies,state =>
      let q := P.ask ⟨t,by omega⟩ seed replies
      let a := oracle state q
      a.2 = A q ∧ ConsistentFrom P oracle A seed k (t + 1) (by omega) (Fin.snoc replies a.2) a.1

def Consistent (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (A : Q → R) (seed : Ω) (state : S) : Prop :=
  ConsistentFrom P oracle A seed T 0 (by omega) Fin.elim0 state

theorem ConsistentFrom.eval_eq (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (A : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S)
    (hc : ConsistentFrom P oracle A seed k t ht replies state) :
    (evalStateFrom P oracle seed k t ht replies state).1 = evalFrom P A seed k t ht replies := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih =>
      have hr := hc.1
      have hh := ih (t + 1) (by omega) _ _ hc.2
      change (evalStateFrom P oracle seed k (t + 1) _ _ _).1 = evalFrom P A seed k (t + 1) _ _
      rw [hh,hr]

theorem Consistent.eval_eq (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (A : Q → R) (seed : Ω) (state : S)
    (hc : Consistent P oracle A seed state) : (evalState P oracle seed state).1 = eval P A seed :=
  ConsistentFrom.eval_eq P oracle A seed T 0 (by omega) Fin.elim0 state hc

theorem evalStateFrom_recordReplies_prefix (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) (i : Fin t) :
    (evalStateFrom (recordReplies P) oracle seed k t ht replies state).1.2 ⟨i.val,by have := i.isLt; omega⟩ = replies i := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih =>
      have hh := ih (t + 1) (by omega)
        (Fin.snoc replies (oracle state (P.ask ⟨t,by omega⟩ seed replies)).2)
        (oracle state (P.ask ⟨t,by omega⟩ seed replies)).1 i.castSucc
      simpa only [evalStateFrom,recordReplies,Fin.val_castSucc,Fin.snoc_castSucc] using hh

theorem consistentFrom_of_recorded_cache (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (A : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S)
    (hc : CacheConsistent P A seed (evalStateFrom (recordReplies P) oracle seed k t ht replies state).1.2) :
    ConsistentFrom P oracle A seed k t ht replies state := by
  induction k generalizing t state with
  | zero => trivial
  | succ k ih =>
      have hlt : t < T := by omega
      let q := P.ask ⟨t,hlt⟩ seed replies
      let a := oracle state q
      let cache := (evalStateFrom (recordReplies P) oracle seed (k + 1) t ht replies state).1.2
      have hp : cachePrefix cache ⟨t,hlt⟩ = replies := by
        funext i
        exact evalStateFrom_recordReplies_prefix P oracle seed (k + 1) t ht replies state i
      have ha : cache ⟨t,hlt⟩ = a.2 := by
        have hh := evalStateFrom_recordReplies_prefix P oracle seed k (t + 1) (by omega)
          (Fin.snoc replies a.2) a.1 (Fin.last t)
        simpa only [cache,evalStateFrom,recordReplies,q,a,Fin.val_last,Fin.snoc_last] using hh
      have he : A (P.ask ⟨t,hlt⟩ seed (cachePrefix cache ⟨t,hlt⟩)) = cache ⟨t,hlt⟩ := hc ⟨t,hlt⟩
      rw [hp,ha] at he
      refine ⟨he.symm,?_⟩
      exact ih (t + 1) (by omega) (Fin.snoc replies a.2) a.1 hc

theorem consistent_of_recorded_cache (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (A : Q → R) (seed : Ω) (state : S)
    (hc : CacheConsistent P A seed (evalState (recordReplies P) oracle seed state).1.2) :
    Consistent P oracle A seed state :=
  consistentFrom_of_recorded_cache P oracle A seed T 0 (by omega) Fin.elim0 state hc

theorem evalStateFrom_recordReplies_finish (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    (evalStateFrom (recordReplies P) oracle seed k t ht replies state).1.1 =
      P.finish seed (evalStateFrom (recordReplies P) oracle seed k t ht replies state).1.2 := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _ _

theorem evalState_recordReplies_finish (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    (evalState (recordReplies P) oracle seed state).1.1 = P.finish seed (evalState (recordReplies P) oracle seed state).1.2 :=
  evalStateFrom_recordReplies_finish P oracle seed T 0 (by omega) Fin.elim0 state

theorem evalStateFrom_recordReplies_forget (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    Prod.map Prod.fst id (evalStateFrom (recordReplies P) oracle seed k t ht replies state) =
      evalStateFrom P oracle seed k t ht replies state := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _ _

theorem evalState_recordReplies_forget (P : Fixed Q R X Ω T) (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    Prod.map Prod.fst id (evalState (recordReplies P) oracle seed state) = evalState P oracle seed state :=
  evalStateFrom_recordReplies_forget P oracle seed T 0 (by omega) Fin.elim0 state

end NCConcave16991.OracleProgram
