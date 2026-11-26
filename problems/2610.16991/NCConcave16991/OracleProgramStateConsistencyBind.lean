import NCConcave16991.OracleProgramStateConsistency
import NCConcave16991.OracleProgramStateBind
import NCConcave16991.OracleProgramLibrary

/-! # Actual reply consistency splits through sequential program composition -/

namespace NCConcave16991.OracleProgram

variable {Q R X Y Ω S : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {T U : ℕ}

private theorem c_prefix (a : Fin T → R) (b : Fin s → R) :
    (fun i : Fin T ↦ Fin.append a b ⟨i.val,by omega⟩) = a := funext (Fin.append_left a b)

private theorem c_ask_congr (P : Fixed Q R Y Ω U) (seed : Ω) (i j : Fin U) (hij : i = j)
    (a : Fin i.val → R) (b : Fin j.val → R)
    (hab : ∀ k, a k = b (Fin.cast (congrArg Fin.val hij) k)) : P.ask i seed a = P.ask j seed b := by
  subst j
  congr 1
  funext k
  exact hab k

private theorem c_bind_ask (P : Fixed Q R X Ω T) (N : Fixed Q R Y (Ω × X) U)
    (seed : Ω) (s : ℕ) (hs : s < U) (a : Fin T → R) (b : Fin s → R) :
    (bind P N).ask ⟨T + s,by omega⟩ seed (Fin.append a b) = N.ask ⟨s,hs⟩ (seed,P.finish seed a) b := by
  have hn : ¬ T + s < T := by omega
  have hsub : T + s - T = s := by omega
  simp only [bind,hn,dite_false]
  change N.ask ⟨T + s - T,by omega⟩ (seed,P.finish seed (fun i : Fin T ↦ Fin.append a b ⟨i.val,by omega⟩))
    (fun i : Fin (T + s - T) ↦ Fin.append a b ⟨T + i.val,by omega⟩) = _
  rw [c_prefix]
  apply c_ask_congr N (seed,P.finish seed a) _ _ (Fin.ext hsub)
  intro i
  have hi : i.val < T + s - T := i.isLt
  exact Fin.append_right a b ⟨i.val,by omega⟩

theorem consistentFrom_bind_second (P : Fixed Q R X Ω T) (N : Fixed Q R Y (Ω × X) U)
    (oracle : S → Q → S × R) (A : Q → R) (seed : Ω) (k s : ℕ) (hs : s + k = U)
    (a : Fin T → R) (b : Fin s → R) (state : S) :
    ConsistentFrom (bind P N) oracle A seed k (T + s) (by omega) (Fin.append a b) state ↔
      ConsistentFrom N oracle A (seed,P.finish seed a) k s hs b state := by
  induction k generalizing s state with
  | zero => rfl
  | succ k ih =>
      have hsu : s < U := by omega
      simp only [ConsistentFrom,c_bind_ask P N seed s hsu a b]
      rw [← Fin.append_snoc]
      exact and_congr_right (fun _ ↦ ih (s + 1) (by omega) _ _)

theorem consistentFrom_bind_first (P : Fixed Q R X Ω T) (N : Fixed Q R Y (Ω × X) U)
    (oracle : S → Q → S × R) (A : Q → R) (seed : Ω) (k t : ℕ) (ht : t + k = T)
    (replies : Fin t → R) (state : S) :
    ConsistentFrom (bind P N) oracle A seed (k + U) t (by omega) replies state ↔
      ConsistentFrom P oracle A seed k t ht replies state ∧
        let a := evalStateFrom P oracle seed k t ht replies state
        Consistent N oracle A (seed,a.1) a.2 := by
  induction k generalizing t state with
  | zero =>
      have he : t = T := by omega
      subst t
      have hh := consistentFrom_bind_second P N oracle A seed U 0 (by omega) replies Fin.elim0 state
      simpa only [ConsistentFrom,Consistent,evalStateFrom,Fin.append_elim0,Fin.cast_refl,
        Function.id_def,Function.comp_def,Nat.zero_add,Nat.add_zero,true_and] using hh
  | succ k ih =>
      have hlt : t < T := by omega
      have ha : (bind P N).ask ⟨t,by omega⟩ seed replies = P.ask ⟨t,hlt⟩ seed replies := by
        simp only [bind,hlt,dite_true]
      simp only [Nat.succ_add,ConsistentFrom,evalStateFrom,ha]
      rw [ih (t + 1) (by omega)]
      exact and_assoc.symm

theorem consistent_bind (P : Fixed Q R X Ω T) (N : Fixed Q R Y (Ω × X) U)
    (oracle : S → Q → S × R) (A : Q → R) (seed : Ω) (state : S) :
    Consistent (bind P N) oracle A seed state ↔ Consistent P oracle A seed state ∧
      let a := evalState P oracle seed state
      Consistent N oracle A (seed,a.1) a.2 :=
  consistentFrom_bind_first P N oracle A seed T 0 (by omega) Fin.elim0 state

theorem Consistent.fullPass_replies (queries : Ω → Fin T → Q)
    (hq : ∀ i, Measurable (fun seed ↦ queries seed i)) (oracle : S → Q → S × R) (A : Q → R)
    (seed : Ω) (state : S) (hc : Consistent (fullPass (R := R) queries hq) oracle A seed state) :
    (evalState (fullPass (R := R) queries hq) oracle seed state).1 = (fun i ↦ A (queries seed i)) :=
  (Consistent.eval_eq _ oracle A seed state hc).trans (eval_fullPass queries hq A seed)

end NCConcave16991.OracleProgram
