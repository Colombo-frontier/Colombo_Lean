import SecondOrder.CurvatureContinuationCoupling

open scoped Classical

namespace SecondOrder
noncomputable section
variable {S A : Type}

/-- Append a fresh coefficient history, retaining the original initial state. -/
def finiteHistoryAppend (n : ℕ) (h : FiniteHistory S A n) :
    (k : ℕ) → FiniteHistory Unit A k → FiniteHistory S A (n+k)
  | 0, _ => h
  | k+1, u => (finiteHistoryAppend n h k u.1,u.2)

def finiteHistoryPrefix (n : ℕ) : (k : ℕ) → FiniteHistory S A (n+k) → FiniteHistory S A n
  | 0, h => h
  | k+1, h => finiteHistoryPrefix n k h.1

def finiteHistorySuffix (n : ℕ) : (k : ℕ) → FiniteHistory S A (n+k) → FiniteHistory Unit A k
  | 0, _ => ()
  | k+1, h => (finiteHistorySuffix n k h.1,h.2)

@[simp] theorem finiteHistoryPrefix_append (n : ℕ) (h : FiniteHistory S A n) :
    ∀ k u, finiteHistoryPrefix n k (finiteHistoryAppend n h k u)=h := by
  intro k
  induction k with
  | zero => intro u; rfl
  | succ k ih => intro u; exact ih u.1

@[simp] theorem finiteHistorySuffix_append (n : ℕ) (h : FiniteHistory S A n) :
    ∀ k u, finiteHistorySuffix n k (finiteHistoryAppend n h k u)=u := by
  intro k
  induction k with
  | zero => intro u; cases u; rfl
  | succ k ih => intro u; exact Prod.ext (ih u.1) rfl

@[simp] theorem finiteHistoryAppend_prefix_suffix (n : ℕ) :
    ∀ k (h : FiniteHistory S A (n+k)),
      finiteHistoryAppend n (finiteHistoryPrefix n k h) k (finiteHistorySuffix n k h)=h := by
  intro k
  induction k with
  | zero => intro h; rfl
  | succ k ih => intro h; exact Prod.ext (ih h.1) rfl

/-- Every history has a unique prefix/suffix decomposition. -/
def finiteHistorySplitEquiv (n k : ℕ) :
    FiniteHistory S A (n+k) ≃ FiniteHistory S A n × FiniteHistory Unit A k where
  toFun h := (finiteHistoryPrefix n k h,finiteHistorySuffix n k h)
  invFun u := finiteHistoryAppend n u.1 k u.2
  left_inv := finiteHistoryAppend_prefix_suffix n k
  right_inv u := Prod.ext (finiteHistoryPrefix_append n u.1 k u.2) (finiteHistorySuffix_append n u.1 k u.2)

theorem finiteHistoryTape_append_prefix (a₀ : A) (n : ℕ) (h : FiniteHistory S A n) :
    ∀ k u t, t<n → finiteHistoryTape a₀ (n+k) (finiteHistoryAppend n h k u) t=finiteHistoryTape a₀ n h t := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro u t ht
    change finiteHistoryTape a₀ (n+k+1) (finiteHistoryAppend n h k u.1,u.2) t=finiteHistoryTape a₀ n h t
    rw [finiteHistoryTape_succ_lt a₀ (n+k) _ t (by omega)]
    exact ih u.1 t ht

theorem finiteHistoryTape_append_suffix (a₀ : A) (n : ℕ) (h : FiniteHistory S A n) :
    ∀ k u t, t<k → finiteHistoryTape a₀ (n+k) (finiteHistoryAppend n h k u) (n+t)=finiteHistoryTape a₀ k u t := by
  intro k
  induction k with
  | zero => intros; omega
  | succ k ih =>
    intro u t ht
    change finiteHistoryTape a₀ (n+k+1) (finiteHistoryAppend n h k u.1,u.2) (n+t)=finiteHistoryTape a₀ (k+1) u t
    by_cases he : t=k
    · subst t
      rw [finiteHistoryTape_succ_at a₀ (n+k), finiteHistoryTape_succ_at]
    · rw [finiteHistoryTape_succ_lt a₀ (n+k) _ (n+t) (by omega),
        finiteHistoryTape_succ_lt a₀ k u t (by omega)]
      exact ih u.1 t (by omega)

theorem finiteHistoryInitial_append [Fintype S] [Fintype A] (n : ℕ) (h : FiniteHistory S A n) :
    ∀ k u, finiteHistoryInitial (n+k) (finiteHistoryAppend n h k u)=finiteHistoryInitial n h := by
  intro k
  induction k with
  | zero => intro u; rfl
  | succ k ih => intro u; exact ih u.1

end
end SecondOrder
