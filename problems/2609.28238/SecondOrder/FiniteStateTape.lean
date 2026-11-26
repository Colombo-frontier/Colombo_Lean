import SecondOrder.CurvatureSuccessProbability

open scoped Classical

namespace SecondOrder
noncomputable section
variable {A : Type} {B : Type*}

def stateTapeRun (b₀ : B) (U : ℕ → B → A → B) (z : ℕ → A) : ℕ → B
  | 0 => b₀
  | n+1 => U n (stateTapeRun b₀ U z n) (z n)

theorem stateTapeRun_tape_congr (b₀ : B) (U : ℕ → B → A → B) (z z' : ℕ → A) :
    ∀ n, (∀ t, t<n → z t=z' t) → stateTapeRun b₀ U z n=stateTapeRun b₀ U z' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hz
    rw [stateTapeRun, stateTapeRun, ih (fun t ht => hz t (by omega)), hz n (by omega)]

theorem finiteStateRun_eq_tape [Fintype A] (b₀ : B) (U : ℕ → B → A → B) (a₀ : A) :
    ∀ n h, finiteStateRun b₀ U n h=stateTapeRun b₀ U (finiteHistoryTape a₀ n h) n := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    rw [finiteStateRun, stateTapeRun, ih, finiteHistoryTape_succ_at,
      stateTapeRun_tape_congr b₀ U _ _ n (finiteHistoryTape_succ_lt a₀ n h)]

end
end SecondOrder
