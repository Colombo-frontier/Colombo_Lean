import NCConcave16991.OracleProgramBind
import NCConcave16991.OracleProgramTransform

/-! # Public budget casts, ignored queries, and private-seed program selection -/

namespace NCConcave16991.OracleProgram

variable {Q R X Ω : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Ω] {T U : ℕ}

def castBudget (P : Fixed Q R X Ω T) (h : T = U) : Fixed Q R X Ω U := h ▸ P

theorem eval_castBudget (P : Fixed Q R X Ω T) (h : T = U) (oracle : Q → R) (seed : Ω) :
    eval (castBudget P h) oracle seed = eval P oracle seed := by
  subst U
  rfl

/-- Fixed dummy queries consume only the declared budget and do not change the returned value. -/
def ignoreQueries (T : ℕ) (q : Ω → Q) (hq : Measurable q) (result : Ω → X)
    (hr : Measurable result) : Fixed Q R X Ω T where
  ask _ seed _ := q seed
  finish seed _ := result seed
  ask_measurable _ := hq.comp measurable_fst
  finish_measurable := hr.comp measurable_fst

theorem evalFrom_ignoreQueries (T : ℕ) (q : Ω → Q) (hq : Measurable q)
    (result : Ω → X) (hr : Measurable result) (oracle : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) :
    evalFrom (ignoreQueries T q hq result hr) oracle seed k t ht replies = result seed := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _

theorem eval_ignoreQueries (T : ℕ) (q : Ω → Q) (hq : Measurable q)
    (result : Ω → X) (hr : Measurable result) (oracle : Q → R) (seed : Ω) :
    eval (ignoreQueries (R := R) T q hq result hr) oracle seed = result seed :=
  evalFrom_ignoreQueries T q hq result hr oracle seed T 0 (by omega) Fin.elim0

def padTo (P : Fixed Q R X Ω T) (h : T ≤ U) (q : Ω → Q) (hq : Measurable q) :
    Fixed Q R X Ω U :=
  castBudget (bind P (ignoreQueries (U - T) (fun a : Ω × X => q a.1)
    (hq.comp measurable_fst) Prod.snd measurable_snd)) (by omega)

theorem eval_padTo (P : Fixed Q R X Ω T) (h : T ≤ U) (q : Ω → Q) (hq : Measurable q)
    (oracle : Q → R) (seed : Ω) :
    eval (padTo P h q hq) oracle seed = eval P oracle seed := by
  simp only [padTo, eval_castBudget, eval_bind, eval_ignoreQueries]

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]

/-- A private seed chooses among programs with the same public fixed budget. -/
def select (index : Ω → I) (hi : Measurable index) (program : I → Fixed Q R X Ω T) :
    Fixed Q R X Ω T where
  ask t seed replies := (program (index seed)).ask t seed replies
  finish seed replies := (program (index seed)).finish seed replies
  ask_measurable t := by
    have hm : Measurable (fun a : I × (Ω × (Fin t.val → R)) =>
        (program a.1).ask t a.2.1 a.2.2) :=
      measurable_from_prod_countable_right (fun i => (program i).ask_measurable t)
    exact hm.comp ((hi.comp measurable_fst).prodMk measurable_id)
  finish_measurable := by
    have hm : Measurable (fun a : I × (Ω × (Fin T → R)) =>
        (program a.1).finish a.2.1 a.2.2) :=
      measurable_from_prod_countable_right (fun i => (program i).finish_measurable)
    exact hm.comp ((hi.comp measurable_fst).prodMk measurable_id)

theorem evalFrom_select (index : Ω → I) (hi : Measurable index)
    (program : I → Fixed Q R X Ω T) (oracle : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) :
    evalFrom (select index hi program) oracle seed k t ht replies =
      evalFrom (program (index seed)) oracle seed k t ht replies := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _

theorem eval_select (index : Ω → I) (hi : Measurable index)
    (program : I → Fixed Q R X Ω T) (oracle : Q → R) (seed : Ω) :
    eval (select index hi program) oracle seed = eval (program (index seed)) oracle seed :=
  evalFrom_select index hi program oracle seed T 0 (by omega) Fin.elim0

end NCConcave16991.OracleProgram
