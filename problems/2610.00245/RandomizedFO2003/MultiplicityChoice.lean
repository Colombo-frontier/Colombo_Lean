import RandomizedFO2003.RotatedBlock
import Mathlib.Algebra.Order.Floor.Semiring

namespace RandomizedFO2003

open scoped BigOperators

/-- Positive design weights admit integer multiplicities of arbitrarily large
minimum size and total dimension, with any prescribed relative accuracy.
This supplies the deterministic choice preceding spherical concentration. -/
theorem exists_relative_multiplicities {J : ℕ} (ν : Fin J → ℝ)
    (hν : ∀ j, 0 < ν j) (hsum : ∑ j, ν j = 1)
    (δ : ℝ) (hδ : 0 < δ) (R N : ℕ) :
    ∃ K : Fin J → ℕ, (∀ j, 0 < K j ∧ R ≤ K j) ∧
      N ≤ ∑ j, K j ∧ 0 < ∑ j, K j ∧
      ∀ j, |(K j : ℝ) / (∑ i, K i : ℕ) - ν j| ≤ δ * ν j := by
  let f : Fin J → ℝ := fun j => max (((R : ℝ) + 1) / ν j)
    (((J : ℝ) + 1) / (δ * ν j))
  obtain ⟨B, hB⟩ := Finite.bddAbove_range f
  obtain ⟨n, hn⟩ := exists_nat_gt (max B (max (N : ℝ) 1))
  have hnB : B < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hnN : (N : ℝ) < n := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hn
  have hn1 : (1 : ℝ) < n := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlarge (j : Fin J) : f j ≤ n := (hB ⟨j, rfl⟩).trans hnB.le
  have hsize (j : Fin J) : (R : ℝ) + 1 ≤ (n : ℝ) * ν j := by
    apply (div_le_iff₀ (hν j)).mp
    exact (le_max_left _ _).trans (hlarge j)
  have hacc (j : Fin J) : (J : ℝ) + 1 ≤ (n : ℝ) * (δ * ν j) := by
    apply (div_le_iff₀ (mul_pos hδ (hν j))).mp
    exact (le_max_right _ _).trans (hlarge j)
  let K : Fin J → ℕ := fun j => Nat.ceil ((n : ℝ) * ν j)
  have hroundlo (j : Fin J) : (n : ℝ) * ν j ≤ K j := Nat.le_ceil _
  have hroundhi (j : Fin J) : (K j : ℝ) ≤ (n : ℝ) * ν j + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hn0.le (hν j).le)).le
  have htotlo : (n : ℝ) ≤ (∑ j, K j : ℕ) := by
    calc
      (n : ℝ) = ∑ j, (n : ℝ) * ν j := by rw [← Finset.mul_sum, hsum, mul_one]
      _ ≤ ∑ j, (K j : ℝ) := Finset.sum_le_sum (fun j _ => hroundlo j)
      _ = _ := by simp
  have htothi : ((∑ j, K j : ℕ) : ℝ) ≤ n + J := by
    calc
      ((∑ j, K j : ℕ) : ℝ) = ∑ j, (K j : ℝ) := by simp
      _ ≤ ∑ j, ((n : ℝ) * ν j + 1) := Finset.sum_le_sum (fun j _ => hroundhi j)
      _ = n + J := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
  have htotpos : (0 : ℝ) < (∑ j, K j : ℕ) := hn0.trans_le htotlo
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · intro j
    have hjlo := hroundlo j
    have hj := hsize j
    have hpos : (0 : ℝ) < K j := by nlinarith [show (0 : ℝ) ≤ R from Nat.cast_nonneg R]
    have hR : (R : ℝ) ≤ K j := by linarith
    exact ⟨by exact_mod_cast hpos, by exact_mod_cast hR⟩
  · exact_mod_cast (hnN.le.trans htotlo)
  · exact_mod_cast htotpos
  · intro j
    have hνone : ν j ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (fun i _ => (hν i).le) (Finset.mem_univ j)
    have hlo := mul_le_mul_of_nonneg_right htotlo (hν j).le
    have hhi := mul_le_mul_of_nonneg_right htothi (hν j).le
    have hνJ := mul_le_mul_of_nonneg_left hνone (Nat.cast_nonneg J)
    have hres : |(K j : ℝ) - (∑ i, K i : ℕ) * ν j| ≤ (J : ℝ) + 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [hroundlo j, hroundhi j,
        show (0 : ℝ) ≤ J from Nat.cast_nonneg J]
    have heq : (K j : ℝ) / (∑ i, K i : ℕ) - ν j =
        ((K j : ℝ) - (∑ i, K i : ℕ) * ν j) / (∑ i, K i : ℕ) := by
      rw [sub_div, mul_div_cancel_left₀ _ htotpos.ne']
    rw [heq, abs_div, abs_of_pos htotpos]
    apply (div_le_iff₀ htotpos).mpr
    have hg := mul_le_mul_of_nonneg_right htotlo (mul_pos hδ (hν j)).le
    exact hres.trans ((hacc j).trans (by nlinarith [hg]))

namespace FiniteSpectralDesign

variable {m : ℕ} {γ L e : ℝ} (D : FiniteSpectralDesign m γ L e)

theorem choose_multiplicities (δ : ℝ) (hδ : 0 < δ) (R N : ℕ) :
    ∃ K : Fin D.size → ℕ, (∀ j, 0 < K j ∧ R ≤ K j) ∧
      N ≤ ∑ j, K j ∧ 0 < ∑ j, K j ∧
      ∀ j, |(K j : ℝ) / (∑ i, K i : ℕ) - D.weight j| ≤ δ * D.weight j :=
  exists_relative_multiplicities D.weight D.weight_pos D.weight_sum δ hδ R N

end FiniteSpectralDesign
end RandomizedFO2003
