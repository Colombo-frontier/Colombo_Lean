import FullJet.RandomizedChain

namespace FullJet

/-- All concentration constraints can be met by one finite block dimension.
The required lower bounds are logarithmic in the trial counts. -/
theorem exists_chain_dimension (T N q : ℕ) : ∃ D : ℕ, 0 < D ∧
    32 * Real.log 2 ≤ (5 / 32 : ℝ) ^ 2 * D ∧
    (2 : ℝ) * (q + 1 : ℕ) ≤ Real.exp ((5 / 32 : ℝ) ^ 2 * D / 4) ∧
    2 * (T + 1 : ℕ) ^ 2 * (N + 1 : ℕ) * Real.exp (-((5 / 32 : ℝ) ^ 2 * D / 2)) ≤ 1 / 4 := by
  let a : ℝ := (5 / 32 : ℝ) ^ 2
  let M : ℝ := 2 * (q + 1 : ℕ)
  let K : ℝ := 8 * (T + 1 : ℕ) ^ 2 * (N + 1 : ℕ)
  have ha : 0 < a := by norm_num [a]
  have hM : 0 < M := by dsimp [M]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨D, hD⟩ := exists_nat_gt (max 0 (max (32 * Real.log 2 / a)
    (max (4 * Real.log M / a) (2 * Real.log K / a))))
  have h0 : (0 : ℝ) < D := (le_max_left _ _).trans_lt hD
  have h1 : 32 * Real.log 2 / a < D :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hD
  have h2 : 4 * Real.log M / a < D :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans_lt hD
  have h3 : 2 * Real.log K / a < D :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans_lt hD
  have h1' := (div_lt_iff₀ ha).mp h1
  have h2' := (div_lt_iff₀ ha).mp h2
  have h3' := (div_lt_iff₀ ha).mp h3
  refine ⟨D, by exact_mod_cast h0, ?_, ?_, ?_⟩
  · change 32 * Real.log 2 ≤ a * D
    nlinarith
  · change M ≤ Real.exp (a * D / 4)
    rw [← Real.exp_log hM]
    apply Real.exp_le_exp.mpr
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr (by nlinarith only [h2'])
  · have he : Real.exp (-(a * D / 2)) ≤ K⁻¹ := by
      rw [← Real.exp_log hK, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by nlinarith only [h3'])
    have hc : (0 : ℝ) ≤ 2 * (T + 1 : ℕ) ^ 2 * (N + 1 : ℕ) := by positivity
    refine (mul_le_mul_of_nonneg_left he hc).trans ?_
    have hid : 2 * (T + 1 : ℕ) ^ 2 * (N + 1 : ℕ) * K⁻¹ = 1 / 4 := by
      calc
        _ = (K / 4) * K⁻¹ := by dsimp [K]; ring
        _ = 1 / 4 := by field_simp; ring
    exact hid.le

end FullJet
