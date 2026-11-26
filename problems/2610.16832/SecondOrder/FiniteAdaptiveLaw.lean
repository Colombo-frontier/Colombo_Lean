import SecondOrder.FiniteConditionalEntropy

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

universe u

namespace SecondOrder
noncomputable section

/-- A finite initial state followed by an ordered history of sampled arrays.
Response and query maps may take values in arbitrary spaces. -/
def FiniteHistory (S A : Type u) : ℕ → Type u
  | 0 => S
  | n+1 => FiniteHistory S A n × A

instance finiteHistoryFintype {S A : Type u} [Fintype S] [Fintype A] :
    (n : ℕ) → Fintype (FiniteHistory S A n)
  | 0 => inferInstanceAs (Fintype S)
  | n+1 => @instFintypeProd (FiniteHistory S A n) A (finiteHistoryFintype n) inferInstance

variable {S A : Type u} [Fintype S] [Fintype A]

/-- Each transition may depend on the entire previous history. -/
def finiteAdaptiveLaw (p : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A) :
    (n : ℕ) → PMF (FiniteHistory S A n)
  | 0 => p
  | n+1 => finiteConditionalPMF (finiteAdaptiveLaw p K n) (K n)

@[simp] theorem finiteAdaptiveLaw_zero (p : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A) :
    finiteAdaptiveLaw p K 0=p := rfl

@[simp] theorem finiteAdaptiveLaw_succ (p : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A) (n : ℕ) :
    finiteAdaptiveLaw p K (n+1)=finiteConditionalPMF (finiteAdaptiveLaw p K n) (K n) := rfl

theorem finiteAdaptiveLaw_ne_zero (p : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A)
    (hp : ∀ s, p s≠0) (hK : ∀ n h a, K n h a≠0) :
    ∀ n h, finiteAdaptiveLaw p K n h≠0 := by
  intro n
  induction n with
  | zero => exact hp
  | succ n ih => exact finiteConditionalPMF_ne_zero _ _ ih (hK n)

/-- Initial hidden state, retained throughout the sampled history. -/
def finiteHistoryInitial : (n : ℕ) → FiniteHistory S A n → S
  | 0, h => h
  | n+1, h => finiteHistoryInitial n h.1

theorem finiteAdaptiveLaw_initial_mean (p : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A)
    (f : S → ℝ) : ∀ n, pmfMean (finiteAdaptiveLaw p K n) (fun h => f (finiteHistoryInitial n h))=pmfMean p f := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change pmfMean (finiteConditionalPMF _ _) (fun h => f (finiteHistoryInitial n h.1))=_
    rw [finiteConditionalPMF_mean_fst (finiteAdaptiveLaw p K n) (K n)
      (fun h => f (finiteHistoryInitial n h)), ih]

/-- The realized information charge, evaluated before each sampled response. -/
def finiteHistoryCost (c : ∀ n, FiniteHistory S A n → ℝ) : (n : ℕ) → FiniteHistory S A n → ℝ
  | 0, _ => 0
  | n+1, h => finiteHistoryCost c n h.1+c n h.1

theorem finiteHistoryCost_nonneg (c : ∀ n, FiniteHistory S A n → ℝ) (hc : ∀ n h, 0≤c n h) :
    ∀ n h, 0≤finiteHistoryCost c n h := by
  intro n
  induction n with
  | zero => intro _; exact le_rfl
  | succ n ih => intro h; exact add_nonneg (ih h.1) (hc n h.1)

theorem finiteHistoryCost_mean_succ (p : PMF S) (K : ∀ n, FiniteHistory S A n → PMF A)
    (c : ∀ n, FiniteHistory S A n → ℝ) (n : ℕ) :
    pmfMean (finiteAdaptiveLaw p K (n+1)) (finiteHistoryCost c (n+1)) =
      pmfMean (finiteAdaptiveLaw p K n) (finiteHistoryCost c n)+pmfMean (finiteAdaptiveLaw p K n) (c n) := by
  change pmfMean (finiteConditionalPMF _ _) (fun h => finiteHistoryCost c n h.1+c n h.1)=_
  rw [pmfMean_add, finiteConditionalPMF_mean_fst, finiteConditionalPMF_mean_fst]

/-- Chain-rule upper bound with history-dependent charges, not the worst-case
charge multiplied by the horizon. -/
theorem finiteAdaptiveLaw_pmfKL_le (p q : PMF S)
    (K L : ∀ n, FiniteHistory S A n → PMF A)
    (hp : ∀ s, p s≠0) (hq : ∀ s, q s≠0)
    (hK : ∀ n h a, K n h a≠0) (hL : ∀ n h a, L n h a≠0)
    (c : ∀ n, FiniteHistory S A n → ℝ) (hc : ∀ n h, pmfKL (K n h) (L n h)≤c n h) :
    ∀ n, pmfKL (finiteAdaptiveLaw p K n) (finiteAdaptiveLaw q L n) ≤
      pmfKL p q+pmfMean (finiteAdaptiveLaw p K n) (finiteHistoryCost c n) := by
  intro n
  induction n with
  | zero => simp only [finiteAdaptiveLaw_zero, finiteHistoryCost, pmfMean_const, add_zero, le_refl]
  | succ n ih =>
    have hh := pmfKL_finiteConditional_le (finiteAdaptiveLaw p K n) (finiteAdaptiveLaw q L n)
      (K n) (L n) (finiteAdaptiveLaw_ne_zero p K hp hK n) (finiteAdaptiveLaw_ne_zero q L hq hL n)
      (hK n) (hL n) (c n) (hc n)
    rw [finiteHistoryCost_mean_succ]
    exact hh.trans (by linarith only [ih])

theorem finiteAdaptiveLaw_pmfKL_of_cap (p : PMF S)
    (K L : ∀ n, FiniteHistory S A n → PMF A)
    (hp : ∀ s, p s≠0) (hK : ∀ n h a, K n h a≠0) (hL : ∀ n h a, L n h a≠0)
    (c : ∀ n, FiniteHistory S A n → ℝ) (hc : ∀ n h, pmfKL (K n h) (L n h)≤c n h)
    (n : ℕ) {M : ℝ} (hcap : ∀ h, finiteHistoryCost c n h≤M) :
    pmfKL (finiteAdaptiveLaw p K n) (finiteAdaptiveLaw p L n)≤M := by
  have hh := finiteAdaptiveLaw_pmfKL_le p p K L hp hp hK hL c hc n
  rw [pmfKL_self, zero_add] at hh
  exact hh.trans (pmfMean_le_const _ M hcap)

end
end SecondOrder
