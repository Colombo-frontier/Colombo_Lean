import NCConcave16991.DenseWeakColumnProbability
import NCConcave16991.DenseWeakChannel
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Fixed-column signs and the actual next-sign channel probability -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

variable {I : Type*} [Fintype I] [DecidableEq I]

def columnSign (A : Finset I) (i : I) : ℝ := if i ∈ A then 1 else -1

theorem columnSign_sum (A R : Finset I) :
    (∑ i ∈ R, columnSign A i) = 2 * ((R ∩ A).card : ℝ) - R.card := by
  have he (i : I) : columnSign A i = 2 * (if i ∈ A then (1 : ℝ) else 0) - 1 := by
    by_cases h : i ∈ A <;> norm_num [columnSign, h]
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem columnSign_total {k : ℕ} (A : PositiveColumn I k) :
    (∑ i : I, columnSign A.val i) = 2 * (k : ℝ) - Fintype.card I := by
  simpa only [Finset.univ_inter, A.property, Finset.card_univ] using columnSign_sum A.val Finset.univ

theorem columnSign_observed {k : ℕ} {R B : Finset I} (A : ObservedColumn k R B) :
    (∑ i ∈ R, columnSign A.val.val i) = 2 * (B.card : ℝ) - R.card := by
  have h := columnSign_sum A.val.val R
  rw [Finset.inter_comm R A.val.val, A.property] at h
  exact h

theorem nextSignProbability_of_counts {n k d c : ℕ} {m σ θ : ℝ}
    (hck : c ≤ k) (hdn : d ≤ n)
    (hencode : 2 * (k : ℝ) - n = m * θ) (hobs : 2 * (c : ℝ) - d = σ) :
    ((k - c : ℕ) : ℝ) / ((n - d : ℕ) : ℝ) = nextSignProbability n m d σ θ := by
  rw [Nat.cast_sub hck, Nat.cast_sub hdn]
  unfold nextSignProbability
  have he : (n : ℝ) + m * θ - d - σ = 2 * ((k : ℝ) - c) := by
    linarith only [hencode, hobs]
  rw [he]
  field_simp
  <;> ring

/-- The literal next-sign formula is derived from the original static column
law conditioned on its actual observed signs, not assumed as a transition law. -/
theorem conditional_nextSign_probability {k : ℕ} {R B : Finset I}
    (hk : k ≤ Fintype.card I) (hB : B ⊆ R) (hBk : B.card ≤ k)
    [Nonempty (ObservedColumn k R B)] (j : UnseenRows R) {m θ : ℝ}
    (hencode : 2 * (k : ℝ) - Fintype.card I = m * θ)
    [MeasurableSpace (PositiveColumn I k)] [MeasurableSingletonClass (PositiveColumn I k)] :
    (columnLaw I k hk).law.real {A | A.val ∩ R = B ∧ j.val ∈ A.val} /
      (columnLaw I k hk).law.real {A | A.val ∩ R = B} =
      nextSignProbability (Fintype.card I) m R.card (2 * (B.card : ℝ) - R.card) θ := by
  rw [conditional_column_row_probability hk hB hBk j]
  have hd : R.card ≤ Fintype.card I := by
    simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ R)
  exact nextSignProbability_of_counts hBk hd hencode rfl

end NCConcave16991.DenseWeakHiding
