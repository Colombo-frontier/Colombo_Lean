import NCConcave16991.OracleProgramStateLibrary
import NCConcave16991.OracleProgramStateBind

/-! # Stateful dummy queries and exact public-budget padding -/

namespace NCConcave16991.OracleProgram

variable {Q R X Ω S : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Ω] {T U : ℕ}

theorem evalStateFrom_ignoreQueries (T : ℕ) (q : Ω → Q) (hq : Measurable q)
    (result : Ω → X) (hr : Measurable result) (oracle : S → Q → S × R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    evalStateFrom (ignoreQueries T q hq result hr) oracle seed k t ht replies state =
      (result seed,(executeBatchFrom (fun _ : Fin T ↦ q seed) oracle k t ht replies state).2) := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _ _

theorem evalState_ignoreQueries (T : ℕ) (q : Ω → Q) (hq : Measurable q)
    (result : Ω → X) (hr : Measurable result) (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    evalState (ignoreQueries T q hq result hr) oracle seed state =
      (result seed,(executeBatch (fun _ : Fin T ↦ q seed) oracle state).2) :=
  evalStateFrom_ignoreQueries T q hq result hr oracle seed T 0 (by omega) Fin.elim0 state

theorem evalState_padTo (P : Fixed Q R X Ω T) (h : T ≤ U) (q : Ω → Q) (hq : Measurable q)
    (oracle : S → Q → S × R) (seed : Ω) (state : S) :
    evalState (padTo P h q hq) oracle seed state =
      let a := evalState P oracle seed state
      (a.1,(executeBatch (fun _ : Fin (U - T) ↦ q seed) oracle a.2).2) := by
  simp only [padTo,evalState_castBudget,evalState_bind,evalState_ignoreQueries]

end NCConcave16991.OracleProgram
