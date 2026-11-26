import FullJet.BoundedOracleProgram

namespace FullJet.OracleProgram

variable {Q R X : Type}

/-- Pad a bounded trial to a fixed number of actual queries. The fallback
output is used only outside the proved bound. -/
def pad (fallbackQuery : Q) (fallbackOutput : X) : ℕ → OracleProgram Q R X → OracleProgram Q R X
  | 0, P => .done (P.currentOutput fallbackOutput)
  | N + 1, P => .ask (P.currentQuery fallbackQuery)
      (fun r => pad fallbackQuery fallbackOutput N (P.feed r))

theorem pad_uses (fallbackQuery : Q) (fallbackOutput : X) (N : ℕ) (P : OracleProgram Q R X) :
    (P.pad fallbackQuery fallbackOutput N).Uses N := by
  induction N generalizing P with
  | zero => exact Uses.done _
  | succ N ih => exact Uses.ask _ _ N (fun r => ih _)

theorem eval_pad_done (fallbackQuery : Q) (fallbackOutput : X) (oracle : Q → R) (N : ℕ) (x : X) :
    (pad fallbackQuery fallbackOutput N (.done x)).eval oracle = x := by
  induction N with
  | zero => rfl
  | succ N ih => exact ih

theorem eval_pad (fallbackQuery : Q) (fallbackOutput : X) (oracle : Q → R)
    {P : OracleProgram Q R X} {N : ℕ} (hP : P.Within N) :
    (P.pad fallbackQuery fallbackOutput N).eval oracle = P.eval oracle := by
  induction hP with
  | done x N => exact eval_pad_done fallbackQuery fallbackOutput oracle N x
  | ask q k N next ih => exact ih (oracle q)

theorem eval_feed (fallbackQuery : Q) (oracle : Q → R) (P : OracleProgram Q R X) :
    (P.feed (oracle (P.currentQuery fallbackQuery))).eval oracle = P.eval oracle := by
  cases P <;> rfl

end FullJet.OracleProgram
