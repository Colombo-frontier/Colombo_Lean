import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Exact real powers, floor losses, and the two dimension regimes. -/

namespace LowRank

noncomputable def accuracyScale (ε : ℝ) : ℝ := ε ^ (-(1 : ℝ) / 3)

noncomputable def targetRate (N k : ℕ) (ε : ℝ) : ℝ :=
  min (N : ℝ) ((k : ℝ) * accuracyScale ε)

theorem accuracyScale_pos {ε : ℝ} (hε : 0 < ε) : 0 < accuracyScale ε :=
  Real.rpow_pos_of_pos hε _

theorem accuracyScale_cube {ε : ℝ} (hε : 0 < ε) : ε * accuracyScale ε ^ 3 = 1 := by
  unfold accuracyScale
  rw [← Real.rpow_mul_natCast hε.le]
  norm_num
  simpa only [Real.rpow_neg_one] using mul_inv_cancel₀ hε.ne'

theorem targetRate_pos {N k : ℕ} {ε : ℝ} (hN : 0 < N) (hk : 0 < k)
    (hε : 0 < ε) : 0 < targetRate N k ε := by
  exact lt_min (Nat.cast_pos.mpr hN) (mul_pos (Nat.cast_pos.mpr hk) (accuracyScale_pos hε))

/-- Explicit choices replace the draft's informal order of choosing constants.
The threshold `202 k < η R` implies all required dimension inequalities. -/
theorem hard_dimension_exists {N k : ℕ} {ε η : ℝ}
    (hk : 1 ≤ k) (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1)
    (hlarge : 202 * (k : ℝ) < η * targetRate N k ε) :
    ∃ d : ℕ, d ≤ N ∧ (100 : ℝ) * k ≤ d ∧
      (d : ℝ) ≤ η * (k : ℝ) * accuracyScale ε ∧
      η * targetRate N k ε / 2 ≤ d := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : 0 < η * targetRate N k ε := by linarith
  have hR : 0 ≤ targetRate N k ε := (nonneg_of_mul_nonneg_right ht.le hη)
  let d := ⌊η * targetRate N k ε⌋₊
  have hdle : (d : ℝ) ≤ η * targetRate N k ε := Nat.floor_le ht.le
  have hdlt : η * targetRate N k ε < (d : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · have hN : (d : ℝ) ≤ N := calc
      _ ≤ η * targetRate N k ε := hdle
      _ ≤ 1 * targetRate N k ε := mul_le_mul_of_nonneg_right hη1 hR
      _ ≤ N := by simpa [targetRate] using (min_le_left (N : ℝ) ((k : ℝ) * accuracyScale ε))
    exact_mod_cast hN
  · linarith
  · calc
      _ ≤ η * targetRate N k ε := hdle
      _ ≤ η * ((k : ℝ) * accuracyScale ε) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hη.le
      _ = _ := by ring
  · linarith

theorem dimension_implies_cubic_smallness {ε η d k : ℝ}
    (hε : 0 < ε) (hd : 0 ≤ d) (hbound : d ≤ η * k * accuracyScale ε) :
    ε * d ^ 3 ≤ η ^ 3 * k ^ 3 := by
  have hpow := pow_le_pow_left₀ hd hbound 3
  have hmul := mul_le_mul_of_nonneg_left hpow hε.le
  have heq : ε * (η * k * accuracyScale ε) ^ 3 = η ^ 3 * k ^ 3 := by
    calc
      _ = (η ^ 3 * k ^ 3) * (ε * accuracyScale ε ^ 3) := by ring
      _ = _ := by rw [accuracyScale_cube hε, mul_one]
  exact hmul.trans_eq heq

/-- Arithmetic combination of a rank baseline and a hard-dimension baseline.
This lemma does not assert either oracle lower bound. -/
theorem combine_two_regimes {Q R k η : ℝ}
    (hη : 0 < η) (hR : 0 ≤ R) (hbaseline : k ≤ Q)
    (hhard : 202 * k < η * R → η * R / 200 ≤ Q) :
    (η / 202) * R ≤ Q := by
  by_cases h : 202 * k < η * R
  · have hq := hhard h
    have hprod := mul_nonneg hη.le hR
    linarith
  · push_neg at h
    linarith

end LowRank
