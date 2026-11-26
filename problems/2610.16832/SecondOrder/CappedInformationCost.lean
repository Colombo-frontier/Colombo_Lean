import SecondOrder.FiniteAdaptiveLaw

open MeasureTheory InformationTheory
open scoped Classical ENNReal

universe u

namespace SecondOrder
noncomputable section
variable {S A : Type u} [Fintype S] [Fintype A]

/-- Count selected responses, freezing at the prescribed cap. Selection is
allowed to depend on the entire pre-response history. -/
def cappedHistoryCount (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ) :
    (n : ℕ) → FiniteHistory S A n → ℕ
  | 0, _ => 0
  | n+1, h => cappedHistoryCount select cap n h.1+
      if cappedHistoryCount select cap n h.1<cap ∧ select n h.1=true then 1 else 0

theorem cappedHistoryCount_le (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ) :
    ∀ n h, cappedHistoryCount select cap n h≤cap := by
  intro n
  induction n with
  | zero => intro _; exact Nat.zero_le _
  | succ n ih =>
    intro h
    have hh := ih h.1
    simp only [cappedHistoryCount]
    split_ifs <;> omega

def cappedHistoryCharge (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ) (κ : ℝ)
    (n : ℕ) (h : FiniteHistory S A n) : ℝ :=
  if cappedHistoryCount select cap n h<cap ∧ select n h=true then κ else 0

theorem cappedHistoryCharge_total (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ) (κ : ℝ) :
    ∀ n h, finiteHistoryCost (cappedHistoryCharge select cap κ) n h = κ*cappedHistoryCount select cap n h := by
  intro n
  induction n with
  | zero => intro _; simp [finiteHistoryCost, cappedHistoryCount]
  | succ n ih =>
    intro h
    simp only [finiteHistoryCost, ih, cappedHistoryCharge, cappedHistoryCount]
    split_ifs <;> simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] <;> ring

/-- After the cap, use a common law in both experiments. A deterministic
dummy reply may be returned by the response map, without a positive-mass
assumption on the observable response space. -/
def cappedTransition (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ)
    (K D : ∀ n, FiniteHistory S A n → PMF A) (n : ℕ) (h : FiniteHistory S A n) : PMF A :=
  if cappedHistoryCount select cap n h<cap then K n h else D n h

theorem cappedTransition_ne_zero (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ)
    (K D : ∀ n, FiniteHistory S A n → PMF A)
    (hK : ∀ n h a, K n h a≠0) (hD : ∀ n h a, D n h a≠0) :
    ∀ n h a, cappedTransition select cap K D n h a≠0 := by
  intro n h a
  unfold cappedTransition
  split_ifs
  · exact hK n h a
  · exact hD n h a

theorem cappedTransition_pmfKL_le (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ)
    (K L D : ∀ n, FiniteHistory S A n → PMF A) (κ : ℝ)
    (hKL : ∀ n h, pmfKL (K n h) (L n h)≤ if select n h=true then κ else 0) :
    ∀ n h, pmfKL (cappedTransition select cap K D n h) (cappedTransition select cap L D n h)≤
      cappedHistoryCharge select cap κ n h := by
  intro n h
  by_cases hc : cappedHistoryCount select cap n h<cap
  · simpa only [cappedTransition, if_pos hc, cappedHistoryCharge, hc, true_and] using hKL n h
  · simp only [cappedTransition, if_neg hc, cappedHistoryCharge, hc, false_and, if_false, pmfKL_self, le_refl]

/-- The joint hidden-state/coefficient-history experiment spends at most
cap*κ information, regardless of the deterministic query horizon. -/
theorem cappedAdaptiveLaw_pmfKL_le (p : PMF S)
    (select : ∀ n, FiniteHistory S A n → Bool) (cap : ℕ)
    (K L D : ∀ n, FiniteHistory S A n → PMF A)
    (hp : ∀ s, p s≠0) (hK : ∀ n h a, K n h a≠0)
    (hL : ∀ n h a, L n h a≠0) (hD : ∀ n h a, D n h a≠0)
    {κ : ℝ} (hκ : 0≤κ)
    (hKL : ∀ n h, pmfKL (K n h) (L n h)≤ if select n h=true then κ else 0) (n : ℕ) :
    pmfKL (finiteAdaptiveLaw p (cappedTransition select cap K D) n)
      (finiteAdaptiveLaw p (cappedTransition select cap L D) n)≤κ*cap := by
  apply finiteAdaptiveLaw_pmfKL_of_cap p _ _ hp
    (cappedTransition_ne_zero select cap K D hK hD)
    (cappedTransition_ne_zero select cap L D hL hD)
    (cappedHistoryCharge select cap κ) (cappedTransition_pmfKL_le select cap K L D κ hKL) n
  intro h
  rw [cappedHistoryCharge_total]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast cappedHistoryCount_le select cap n h) hκ

end
end SecondOrder
