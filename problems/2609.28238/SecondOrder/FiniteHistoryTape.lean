import SecondOrder.ComparisonStageEntry

open scoped Classical ENNReal

universe u

namespace SecondOrder
noncomputable section

/-- A finite coefficient history extended by a fixed unused value. -/
def finiteHistoryTape {S A : Type u} (a₀ : A) : (n : ℕ) → FiniteHistory S A n → ℕ → A
  | 0, _, _ => a₀
  | n+1, h, t => if t=n then h.2 else finiteHistoryTape a₀ n h.1 t

theorem finiteHistoryTape_succ_lt {S A : Type u} (a₀ : A) (n : ℕ)
    (h : FiniteHistory S A (n+1)) (t : ℕ) (ht : t<n) :
    finiteHistoryTape a₀ (n+1) h t=finiteHistoryTape a₀ n h.1 t := by
  simp only [finiteHistoryTape, if_neg (Nat.ne_of_lt ht)]

@[simp] theorem finiteHistoryTape_succ_at {S A : Type u} (a₀ : A) (n : ℕ)
    (h : FiniteHistory S A (n+1)) : finiteHistoryTape a₀ (n+1) h n=h.2 := by
  simp [finiteHistoryTape]

theorem finiteHistoryTape_unused {S A : Type u} (a₀ : A) :
    ∀ n (h : FiniteHistory S A n) t, n≤t → finiteHistoryTape a₀ n h t=a₀ := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro h t ht
    rw [finiteHistoryTape, if_neg (by omega)]
    exact ih h.1 t (by omega)

theorem finiteHistoryTape_default_congr {S A : Type u} (a₀ a₁ : A) :
    ∀ n (h : FiniteHistory S A n) t, t<n →
      finiteHistoryTape a₀ n h t=finiteHistoryTape a₁ n h t := by
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro h t ht
    by_cases he : t=n
    · simp only [finiteHistoryTape, if_pos he]
    · simp only [finiteHistoryTape, if_neg he]
      exact ih h.1 t (by omega)

end
end SecondOrder
