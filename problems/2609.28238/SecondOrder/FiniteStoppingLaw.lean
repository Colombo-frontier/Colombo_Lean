import SecondOrder.HiddenConditionalContinuation

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {S A : Type} [Fintype S] [Fintype A]

def finiteHistorySeen (E : ∀ n, FiniteHistory S A n → Prop) :
    (n : ℕ) → FiniteHistory S A n → Prop
  | 0, h => E 0 h
  | n+1, h => finiteHistorySeen E n h.1 ∨ E (n+1) h

def finiteHistoryBefore (E : ∀ n, FiniteHistory S A n → Prop) :
    (n : ℕ) → FiniteHistory S A n → Prop
  | 0, _ => True
  | n+1, h => ¬finiteHistorySeen E n h.1

/-- The first exit satisfies the specified success condition. -/
def finiteHistoryMarked (E F : ∀ n, FiniteHistory S A n → Prop) :
    (n : ℕ) → FiniteHistory S A n → Prop
  | 0, h => F 0 h
  | n+1, h => finiteHistoryMarked E F n h.1 ∨ (¬finiteHistorySeen E n h.1 ∧ F (n+1) h)

theorem finiteHistoryBefore_of_not_seen (E : ∀ n, FiniteHistory S A n → Prop) :
    ∀ n h, ¬finiteHistorySeen E n h → finiteHistoryBefore E n h := by
  intro n
  cases n with
  | zero => intros; trivial
  | succ n => intro h hh he; exact hh (Or.inl he)

theorem finiteHistoryMarked_seen (E F : ∀ n, FiniteHistory S A n → Prop)
    (hFE : ∀ n h, F n h → E n h) :
    ∀ n h, finiteHistoryMarked E F n h → finiteHistorySeen E n h := by
  intro n
  induction n with
  | zero => intro h hh; exact hFE 0 h hh
  | succ n ih =>
    intro h hh
    rcases hh with hh | hh
    · exact Or.inl (ih h.1 hh)
    · exact Or.inr (hFE (n+1) h hh.2)

theorem finiteHistoryMarked_seen_success (E F : ∀ n, FiniteHistory S A n → Prop) :
    ∀ n h, finiteHistoryMarked E F n h → finiteHistorySeen F n h := by
  intro n
  induction n with
  | zero => intro h hh; exact hh
  | succ n ih =>
    intro h hh
    rcases hh with hh | hh
    · exact Or.inl (ih h.1 hh)
    · exact Or.inr hh.2

/-- Agreement of transition probabilities before an exit gives exact
agreement of the probability of every history up to and including first exit. -/
theorem finiteAdaptiveLaw_before_mass (p : PMF S)
    (K L : ∀ n, FiniteHistory S A n → PMF A) (E : ∀ n, FiniteHistory S A n → Prop)
    (hKL : ∀ n h, ¬finiteHistorySeen E n h → K n h=L n h) :
    ∀ n h, finiteHistoryBefore E n h → finiteAdaptiveLaw p K n h=finiteAdaptiveLaw p L n h := by
  intro n
  induction n with
  | zero => intro h hh; rfl
  | succ n ih =>
    intro h hh
    change finiteAdaptiveLaw p K n h.1*K n h.1 h.2=finiteAdaptiveLaw p L n h.1*L n h.1 h.2
    rw [ih h.1 (finiteHistoryBefore_of_not_seen E n h.1 hh), hKL n h.1 hh]

theorem finiteAdaptiveLaw_first_mean (p : PMF S)
    (K L : ∀ n, FiniteHistory S A n → PMF A) (E F : ∀ n, FiniteHistory S A n → Prop)
    (hKL : ∀ n h, ¬finiteHistorySeen E n h → K n h=L n h) (n : ℕ) :
    pmfMean (finiteAdaptiveLaw p K n) (fun h => if finiteHistoryBefore E n h ∧ F n h then (1:ℝ) else 0)=
      pmfMean (finiteAdaptiveLaw p L n) (fun h => if finiteHistoryBefore E n h ∧ F n h then (1:ℝ) else 0) := by
  apply Finset.sum_congr rfl
  intro h _
  dsimp only
  by_cases hh : finiteHistoryBefore E n h ∧ F n h
  · rw [if_pos hh, finiteAdaptiveLaw_before_mass p K L E hKL n h hh.1]
  · simp only [if_neg hh, smul_zero]

theorem finiteHistoryMarked_succ_indicator (E F : ∀ n, FiniteHistory S A n → Prop)
    (hFE : ∀ n h, F n h → E n h) (n : ℕ) (h : FiniteHistory S A (n+1)) :
    (if finiteHistoryMarked E F (n+1) h then (1:ℝ) else 0)=
      (if finiteHistoryMarked E F n h.1 then (1:ℝ) else 0)+
      (if finiteHistoryBefore E (n+1) h ∧ F (n+1) h then (1:ℝ) else 0) := by
  have hh := finiteHistoryMarked_seen E F hFE n h.1
  rw [finiteHistoryMarked, finiteHistoryBefore]
  split_ifs <;> norm_num <;> tauto

/-- Equality of the entire first-exit success probability, even if the two
experiments use unrelated kernels after their exit. -/
theorem finiteAdaptiveLaw_stopped_mean (p : PMF S)
    (K L : ∀ n, FiniteHistory S A n → PMF A) (E F : ∀ n, FiniteHistory S A n → Prop)
    (hFE : ∀ n h, F n h → E n h)
    (hKL : ∀ n h, ¬finiteHistorySeen E n h → K n h=L n h) :
    ∀ n, pmfMean (finiteAdaptiveLaw p K n) (fun h => if finiteHistoryMarked E F n h then (1:ℝ) else 0)=
      pmfMean (finiteAdaptiveLaw p L n) (fun h => if finiteHistoryMarked E F n h then (1:ℝ) else 0) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp_rw [finiteHistoryMarked_succ_indicator E F hFE n]
    rw [pmfMean_add, pmfMean_add,
      finiteAdaptiveLaw_first_mean p K L E F hKL (n+1)]
    congr 1
    change pmfMean (finiteConditionalPMF _ _) (fun h => if finiteHistoryMarked E F n h.1 then (1:ℝ) else 0)=
      pmfMean (finiteConditionalPMF _ _) (fun h => if finiteHistoryMarked E F n h.1 then (1:ℝ) else 0)
    rw [finiteConditionalPMF_mean_fst _ _ (fun h => if finiteHistoryMarked E F n h then (1:ℝ) else 0),
      finiteConditionalPMF_mean_fst _ _ (fun h => if finiteHistoryMarked E F n h then (1:ℝ) else 0)]
    exact ih

end
end SecondOrder
