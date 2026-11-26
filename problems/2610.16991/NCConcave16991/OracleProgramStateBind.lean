import NCConcave16991.OracleProgramState

/-! # Stateful sequential composition follows the literal reply chronology -/

namespace NCConcave16991.OracleProgram

variable {Q R X Y Ω S : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {T U : ℕ}

private theorem state_append_prefix (a : Fin T → R) (b : Fin s → R) :
    (fun i : Fin T ↦ Fin.append a b ⟨i.val,by omega⟩) = a := by
  funext i
  exact Fin.append_left a b i

private theorem state_append_suffix (a : Fin T → R) (b : Fin s → R) :
    (fun i : Fin s ↦ Fin.append a b ⟨T + i.val,by omega⟩) = b := by
  funext i
  exact Fin.append_right a b i

private theorem state_ask_congr (P : Fixed Q R Y Ω U) (seed : Ω) (i j : Fin U)
    (hij : i = j) (a : Fin i.val → R) (b : Fin j.val → R)
    (hab : ∀ k, a k = b (Fin.cast (congrArg Fin.val hij) k)) : P.ask i seed a = P.ask j seed b := by
  subst j
  congr 1
  funext k
  exact hab k

private theorem state_bind_ask_second (P : Fixed Q R X Ω T) (N : Fixed Q R Y (Ω × X) U)
    (seed : Ω) (s : ℕ) (hs : s < U) (a : Fin T → R) (b : Fin s → R) :
    (bind P N).ask ⟨T + s,by omega⟩ seed (Fin.append a b) = N.ask ⟨s,hs⟩ (seed,P.finish seed a) b := by
  have hn : ¬ T + s < T := by omega
  have hsub : T + s - T = s := by omega
  simp only [bind,hn,dite_false]
  change N.ask ⟨T + s - T,by omega⟩
    (seed,P.finish seed (fun i : Fin T ↦ Fin.append a b ⟨i.val,by omega⟩))
    (fun i : Fin (T + s - T) ↦ Fin.append a b ⟨T + i.val,by omega⟩) = _
  rw [state_append_prefix]
  apply state_ask_congr N (seed,P.finish seed a) _ _ (Fin.ext hsub)
  intro i
  have hi : i.val < T + s - T := i.isLt
  exact Fin.append_right a b ⟨i.val,by omega⟩

theorem evalStateFrom_bind_second (P : Fixed Q R X Ω T) (N : Fixed Q R Y (Ω × X) U)
    (oracle : S → Q → S × R) (seed : Ω) (k s : ℕ) (hs : s + k = U)
    (a : Fin T → R) (b : Fin s → R) (state : S) :
    evalStateFrom (bind P N) oracle seed k (T + s) (by omega) (Fin.append a b) state =
      evalStateFrom N oracle (seed,P.finish seed a) k s hs b state := by
  induction k generalizing s state with
  | zero =>
      have he : s = U := by omega
      subst s
      change (N.finish (seed,P.finish seed (fun i ↦ Fin.append a b ⟨i.val,by omega⟩))
        (fun i ↦ Fin.append a b ⟨T + i.val,by omega⟩),state) = (N.finish (seed,P.finish seed a) b,state)
      rw [state_append_prefix,state_append_suffix]
  | succ k ih =>
      have hsu : s < U := by omega
      let q := N.ask ⟨s,hsu⟩ (seed,P.finish seed a) b
      change evalStateFrom (bind P N) oracle seed k (T + s + 1) _
        (Fin.snoc (Fin.append a b) (oracle state ((bind P N).ask ⟨T + s,by omega⟩ seed (Fin.append a b))).2)
        (oracle state ((bind P N).ask ⟨T + s,by omega⟩ seed (Fin.append a b))).1 =
        evalStateFrom N oracle (seed,P.finish seed a) k (s + 1) _
          (Fin.snoc b (oracle state q).2) (oracle state q).1
      rw [state_bind_ask_second P N seed s hsu a b,← Fin.append_snoc]
      exact ih (s + 1) (by omega) (Fin.snoc b (oracle state q).2) (oracle state q).1

theorem evalStateFrom_bind_first (P : Fixed Q R X Ω T) (N : Fixed Q R Y (Ω × X) U)
    (oracle : S → Q → S × R) (seed : Ω) (k t : ℕ) (ht : t + k = T)
    (replies : Fin t → R) (state : S) :
    evalStateFrom (bind P N) oracle seed (k + U) t (by omega) replies state =
      let a := evalStateFrom P oracle seed k t ht replies state
      evalState N oracle (seed,a.1) a.2 := by
  induction k generalizing t state with
  | zero =>
      have he : t = T := by omega
      subst t
      have hr := evalStateFrom_bind_second P N oracle seed U 0 (by omega) replies Fin.elim0 state
      simpa only [evalState,evalStateFrom,Fin.append_elim0,Function.comp_def,Fin.cast_refl,
        Function.id_def,Nat.zero_add,Nat.add_zero] using hr
  | succ k ih =>
      have hlt : t < T := by omega
      have ha : (bind P N).ask ⟨t,by omega⟩ seed replies = P.ask ⟨t,hlt⟩ seed replies := by
        simp only [bind,hlt,dite_true]
      simpa only [Nat.succ_add,evalStateFrom,ha] using
        ih (t + 1) (by omega) (Fin.snoc replies (oracle state (P.ask ⟨t,hlt⟩ seed replies)).2)
          (oracle state (P.ask ⟨t,hlt⟩ seed replies)).1

theorem evalState_bind (P : Fixed Q R X Ω T) (N : Fixed Q R Y (Ω × X) U)
    (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    evalState (bind P N) oracle seed state =
      let a := evalState P oracle seed state
      evalState N oracle (seed,a.1) a.2 :=
  evalStateFrom_bind_first P N oracle seed T 0 (by omega) Fin.elim0 state

end NCConcave16991.OracleProgram
