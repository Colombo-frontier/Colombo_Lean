import LowRank.TailEnergyGap

/-! A tail-energy cutoff for every positive power, with the dependence on
the power retained in the number of discarded directions. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

theorem cutoff_le_quarter_of_general_power_budget {E B L c r t : ℝ}
    (hc : 0 ≤ c) (hL : 0 ≤ L) (hr : 0 < r) (hB : 0 < B)
    (ht : (4 : ℝ) ^ r * B ≤ t) (hbudget : t * c ^ r ≤ E)
    (hsmall : E < B * L ^ r) : c ≤ L / 4 := by
  by_contra! hcut
  have hp := Real.rpow_lt_rpow hL (by linarith : L < 4 * c) hr
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hc] at hp
  have hmul := mul_lt_mul_of_pos_left hp hB
  have hcount := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hc r)
  nlinarith

theorem spectral_cutoff_le_quarter_of_general_small_tail {a b k t : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hk : k ≤ b)
    (i : Fin b) (hi : i.val + t ≤ b - k) {p B L : ℝ}
    (hp : 0 < p) (hB : 0 < B) (hL : 0 ≤ L)
    (ht : (4 : ℝ) ^ (p / 2) * B ≤ (t : ℝ))
    (hsmall : optimalSchattenPower p A k < B * L ^ (p / 2)) : sp.value i ≤ L / 4 :=
  cutoff_le_quarter_of_general_power_budget (sp.value_nonneg (rightGram_posSemidef A) i)
    hL (by positivity) hB ht (optimalSchattenPower_ge_tail_count A sp hk i hi hp) hsmall

end
end LowRank
