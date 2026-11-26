import LowRank.GeneralKrylovParameters

/-! The narrow filter takes a cubic-root number of rounds, with all
additional factors depending only on the fixed Schatten exponent. -/

namespace LowRank
noncomputable section

def powerBoostCost (p : ℝ) : ℝ :=
  Real.sqrt (max 1 (p / 2) * (2 : ℝ) ^ (2 * powerBoostOrder p))

theorem powerBoostCost_ge_one (p : ℝ) : 1 ≤ powerBoostCost p := by
  have hpow : (1 : ℝ) ≤ 2 ^ (2 * powerBoostOrder p) := one_le_pow₀ (by norm_num)
  have hprod := one_le_mul_of_one_le_of_one_le (le_max_left 1 (p / 2)) hpow
  simpa only [powerBoostCost, Real.sqrt_one] using Real.sqrt_le_sqrt hprod

theorem powerBoostCost_pos (p : ℝ) : 0 < powerBoostCost p := lt_of_lt_of_le zero_lt_one (powerBoostCost_ge_one p)

theorem sqrt_weightedNarrowGap {p ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (powerBoostedGap (weightedNarrowError p ε) (powerBoostOrder p)) =
      (accuracyScale ε)⁻¹ / powerBoostCost p := by
  unfold powerBoostedGap weightedNarrowError powerBoostCost
  rw [div_div, Real.sqrt_div (cubicKrylovGap_pos hε).le, sqrt_cubicKrylovGap hε]

theorem weightedNarrowDegree_le {p ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    ((chebyshevFilterDegree (powerBoostedGap (weightedNarrowError p ε) (powerBoostOrder p)) η +
      powerBoostOrder p + 1 : ℕ) : ℝ) ≤
        (2 * Real.log (2 / η) * powerBoostCost p + (powerBoostOrder p : ℝ) + 2) * accuracyScale ε := by
  have hd := chebyshevFilterDegree_le (powerBoostedGap_pos (weightedNarrowError_pos (p := p) hε) (powerBoostOrder p)) hη hη1
  rw [sqrt_weightedNarrowGap hε, div_div_eq_mul_div, div_inv_eq_mul] at hd
  have ha := accuracyScale_ge_one hε hε1
  have hv : 0 ≤ (powerBoostOrder p : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith

theorem weightedWideDegree_le {p η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ((chebyshevFilterDegree 1 η + powerBoostOrder p + 1 : ℕ) : ℝ) ≤
      2 * Real.log (2 / η) + (powerBoostOrder p : ℝ) + 2 := by
  have hd := chebyshevFilterDegree_le (by norm_num : (0 : ℝ) < 1) hη hη1
  norm_num only [Real.sqrt_one, div_one] at hd
  push_cast
  linarith

end
end LowRank
