import FullJet.AdaptiveRows
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace FullJet

/-- Conditional probability of the next positive sign. `s` is the sum of
the `d` distinct revealed signs, and `theta` is the hidden sign. -/
noncomputable def nextSignProbability (n m d s theta : ℝ) : ℝ :=
  (n + m * theta - d - s) / (2 * (n - d))

theorem nextSignProbability_bounds (n m d s theta : ℝ)
    (hn : 0 < n) (hm : 0 ≤ m) (hd : 0 ≤ d) (hs : -d ≤ s ∧ s ≤ d)
    (htheta : theta = -1 ∨ theta = 1) (hbudget : 8 * m + 9 * d ≤ n) :
    7 / 16 ≤ nextSignProbability n m d s theta ∧
      nextSignProbability n m d s theta ≤ 9 / 16 := by
  have hden : 0 < 2 * (n - d) := by linarith
  unfold nextSignProbability
  constructor
  · apply (le_div_iff₀ hden).mpr
    rcases htheta with rfl | rfl <;> nlinarith
  · apply (div_le_iff₀ hden).mpr
    rcases htheta with rfl | rfl <;> nlinarith

theorem nextSignProbability_difference (n m d s : ℝ) :
    nextSignProbability n m d s 1 - nextSignProbability n m d s (-1) = m / (n - d) := by
  unfold nextSignProbability
  by_cases h : n - d = 0
  · simp [h]
  · field_simp [h]
    <;> ring

/-- Number of distinct labels in a transcript. -/
def rowHistorySize {α : Type*} [DecidableEq α] (ask : List Bool → α)
    (past bits : List Bool) : ℕ :=
  (positiveLabels ask past bits ∪ negativeLabels ask past bits).card

/-- Sum of the signs revealed at distinct labels in a realizable transcript. -/
def rowHistorySum {α : Type*} [DecidableEq α] (ask : List Bool → α)
    (past bits : List Bool) : ℝ :=
  (positiveLabels ask past bits).card - (negativeLabels ask past bits).card

theorem rowHistorySum_bounds {α : Type*} [DecidableEq α] (ask : List Bool → α)
    (past bits : List Bool) :
    -(rowHistorySize ask past bits : ℝ) ≤ rowHistorySum ask past bits ∧
      rowHistorySum ask past bits ≤ rowHistorySize ask past bits := by
  have hP := Finset.card_le_card
    (Finset.subset_union_left : positiveLabels ask past bits ⊆
      positiveLabels ask past bits ∪ negativeLabels ask past bits)
  have hN := Finset.card_le_card
    (Finset.subset_union_right : negativeLabels ask past bits ⊆
      positiveLabels ask past bits ∪ negativeLabels ask past bits)
  have hP' : ((positiveLabels ask past bits).card : ℝ) ≤ rowHistorySize ask past bits := by
    exact_mod_cast hP
  have hN' : ((negativeLabels ask past bits).card : ℝ) ≤ rowHistorySize ask past bits := by
    exact_mod_cast hN
  have hP0 : (0 : ℝ) ≤ (positiveLabels ask past bits).card := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (negativeLabels ask past bits).card := Nat.cast_nonneg _
  unfold rowHistorySum
  constructor <;> linarith

/-- The algebraic next-sign formula is the probability under the actual
conditional fixed-column law, for any adaptive choice of unrevealed label. -/
theorem fixedSizeLaw_next_probability_signed {n k : ℕ} (hk : k ≤ n)
    (ask : List Bool → Fin n) (past bits : List Bool)
    (hpos : ∃ S ∈ {S | rowAnswers ask S past bits.length = bits},
      S ∈ (fixedSizeLaw Finset.univ k (by simpa using hk)).support)
    (i : Fin n) (hi : i ∉ positiveLabels ask past bits ∪ negativeLabels ask past bits)
    (m theta : ℝ) (hbalance : 2 * (k : ℝ) = n + m * theta) :
    (((fixedSizeLaw Finset.univ k (by simpa using hk)).filter
      {S | rowAnswers ask S past bits.length = bits} hpos).toOuterMeasure {S | i ∈ S}).toReal =
      nextSignProbability n m (rowHistorySize ask past bits) (rowHistorySum ask past bits) theta := by
  let P := positiveLabels ask past bits
  let N := negativeLabels ask past bits
  have hi' : i ∈ (Finset.univ : Finset (Fin n)) \ (P ∪ N) := by simp [hi, P, N]
  have hposCopy := hpos
  obtain ⟨S, hbits, hS⟩ := hposCopy
  have hmem : S ∈ (Finset.univ : Finset (Fin n)).powersetCard k := by
    simpa only [fixedSizeLaw, PMF.mem_support_uniformOfFinset_iff] using hS
  obtain ⟨hP, hPN, hPk, hrem⟩ := compatibleColumn_feasible Finset.univ P N S k hmem
    ((rowAnswers_eq_iff ask S past bits).mp hbits)
  have hd : (P ∪ N).card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ (P ∪ N))
  have hdlt : (P ∪ N).card < n := by
    have hposcard := Finset.card_pos.mpr (show (Finset.univ \ (P ∪ N)).Nonempty from ⟨i, hi'⟩)
    rw [Finset.card_sdiff (Finset.subset_univ _)] at hposcard
    simp only [Finset.card_univ, Fintype.card_fin] at hposcard
    omega
  have hnd : (n : ℝ) - (P ∪ N).card ≠ 0 := by
    have hlt : ((P ∪ N).card : ℝ) < n := by exact_mod_cast hdlt
    linarith
  have hsum : ((P ∪ N).card : ℝ) = (P.card : ℝ) + N.card := by
    exact_mod_cast Finset.card_union_of_disjoint hPN
  rw [fixedSizeLaw_next_probability Finset.univ k (by simpa using hk) ask past bits hpos i hi']
  change ((k - P.card : ℕ) : ℝ) / (Finset.univ \ (P ∪ N)).card =
    nextSignProbability n m (P ∪ N).card ((P.card : ℝ) - N.card) theta
  rw [Finset.card_sdiff (Finset.subset_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_sub hPk, Nat.cast_sub hd]
  unfold nextSignProbability
  rw [hsum] at hnd ⊢
  field_simp [hnd]
  nlinarith

/-- Bernoulli relative entropy, with natural logarithms. All estimates below
are on the interior of the probability interval, so no endpoint convention is needed. -/
noncomputable def bernoulliKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

theorem bernoulliKL_le_chiSquare (p q : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    bernoulliKL p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by
  have h1 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hp hq)) hp.le
  have h2 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1 - p)
      (by linarith : 0 < 1 - q))) (by linarith : 0 ≤ 1 - p)
  have hid : p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) =
      (p - q) ^ 2 / (q * (1 - q)) := by
    field_simp [hq.ne', show 1 - q ≠ 0 by linarith]
    <;> ring
  exact (add_le_add h1 h2).trans_eq hid

theorem bernoulliKL_le_eight_sq (p q : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 / 4 ≤ q) (hq1 : q ≤ 3 / 4) :
    bernoulliKL p q ≤ 8 * (p - q) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hq1' : q < 1 := by linarith
  have hden : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  have hden8 : 1 ≤ 8 * (q * (1 - q)) := by
    nlinarith [mul_nonneg (show 0 ≤ q - 1 / 4 by linarith)
      (show 0 ≤ 3 / 4 - q by linarith)]
  refine (bernoulliKL_le_chiSquare p q hp hp1 hq0 hq1').trans ?_
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_nonneg (sq_nonneg (p - q)) (show 0 ≤ 8 * (q * (1 - q)) - 1 by linarith)]

/-- One revealed coordinate carries at most a constant times squared bias in
Bernoulli relative entropy, uniformly over the compatible short history. -/
theorem nextSignProbability_kl_bound (n m d s : ℝ)
    (hn : 0 < n) (hm : 0 ≤ m) (hd : 0 ≤ d) (hs : -d ≤ s ∧ s ≤ d)
    (hbudget : 8 * m + 9 * d ≤ n) :
    bernoulliKL (nextSignProbability n m d s 1) (nextSignProbability n m d s (-1)) ≤
      32 * (m / n) ^ 2 := by
  have hp := nextSignProbability_bounds n m d s 1 hn hm hd hs (Or.inr rfl) hbudget
  have hq := nextSignProbability_bounds n m d s (-1) hn hm hd hs (Or.inl rfl) hbudget
  have h := bernoulliKL_le_eight_sq (nextSignProbability n m d s 1)
    (nextSignProbability n m d s (-1)) (by linarith [hp.1]) (by linarith [hp.2])
    (by linarith [hq.1]) (by linarith [hq.2])
  rw [nextSignProbability_difference] at h
  have hnd : 0 < n - d := by linarith
  have hratio0 : 0 ≤ m / (n - d) := div_nonneg hm hnd.le
  have hratio : m / (n - d) ≤ 2 * (m / n) := by
    calc
      m / (n - d) ≤ (2 * m) / n := (div_le_div_iff₀ hnd hn).mpr (by
        nlinarith [mul_nonneg hm (show 0 ≤ n - 2 * d by linarith)])
      _ = 2 * (m / n) := by ring
  have hm0 : 0 ≤ m / n := div_nonneg hm hn.le
  nlinarith [sq_nonneg (m / (n - d) - 2 * (m / n))]

/-- Relative entropy bound for the actual next-answer distributions under the
two hidden signs, conditioned on the same realizable adaptive transcript. -/
theorem fixedSizeLaw_next_kl_bound {n kp km : ℕ} (hn : 0 < n)
    (hkp : kp ≤ n) (hkm : km ≤ n) (m : ℝ) (hm : 0 ≤ m)
    (hplus : 2 * (kp : ℝ) = n + m) (hminus : 2 * (km : ℝ) = n - m)
    (ask : List Bool → Fin n) (past bits : List Bool)
    (hposp : ∃ S ∈ {S | rowAnswers ask S past bits.length = bits},
      S ∈ (fixedSizeLaw Finset.univ kp (by simpa using hkp)).support)
    (hposm : ∃ S ∈ {S | rowAnswers ask S past bits.length = bits},
      S ∈ (fixedSizeLaw Finset.univ km (by simpa using hkm)).support)
    (i : Fin n) (hi : i ∉ positiveLabels ask past bits ∪ negativeLabels ask past bits)
    (hbudget : 8 * m + 9 * (rowHistorySize ask past bits : ℝ) ≤ n) :
    bernoulliKL
      ((((fixedSizeLaw Finset.univ kp (by simpa using hkp)).filter
        {S | rowAnswers ask S past bits.length = bits} hposp).toOuterMeasure {S | i ∈ S}).toReal)
      ((((fixedSizeLaw Finset.univ km (by simpa using hkm)).filter
        {S | rowAnswers ask S past bits.length = bits} hposm).toOuterMeasure {S | i ∈ S}).toReal) ≤
      32 * (m / n) ^ 2 := by
  rw [fixedSizeLaw_next_probability_signed hkp ask past bits hposp i hi m 1 (by simpa using hplus),
    fixedSizeLaw_next_probability_signed hkm ask past bits hposm i hi m (-1) (by simpa using hminus)]
  exact nextSignProbability_kl_bound _ _ _ _ (by exact_mod_cast hn) hm (Nat.cast_nonneg _)
    (rowHistorySum_bounds ask past bits) hbudget

end FullJet
