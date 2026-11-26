import FullJet.AmplifiedMethod

namespace FullJet

noncomputable def confidenceRounds (δ : ℝ) : ℕ := ⌈(-Real.log δ) / Real.log 4⌉₊

noncomputable def confidenceFactor (δ : ℝ) : ℝ := 1 + (-Real.log δ) / Real.log 4

theorem confidenceRounds_failure_le (δ : ℝ) (hδ : 0 < δ) :
    (1 / 4 : ℝ) ^ confidenceRounds δ ≤ δ := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc := (div_le_iff₀ h4).mp (Nat.le_ceil ((-Real.log δ) / Real.log 4))
  rw [Real.pow_le_iff_le_log (by norm_num : (0 : ℝ) < 1 / 4) hδ]
  simp only [one_div, Real.log_inv]
  change (confidenceRounds δ : ℝ) * -Real.log 4 ≤ Real.log δ
  change -Real.log δ ≤ (confidenceRounds δ : ℝ) * Real.log 4 at hc
  linarith

theorem confidenceRounds_le (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (confidenceRounds δ : ℝ) ≤ confidenceFactor δ := by
  have hlog : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hnon : 0 ≤ (-Real.log δ) / Real.log 4 := div_nonneg (neg_nonneg.mpr hlog) h4.le
  simpa only [confidenceRounds, confidenceFactor, add_comm] using (Nat.ceil_lt_add_one hnon).le

theorem confidenceFactor_pos (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < confidenceFactor δ := by
  have hlog : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold confidenceFactor
  have := div_nonneg (neg_nonneg.mpr hlog) h4.le
  linarith

theorem confidenceFactor_eq (δ : ℝ) :
    confidenceFactor δ = 1 + Real.log (1 / δ) / Real.log 4 := by
  simp only [confidenceFactor, one_div, Real.log_inv]

end FullJet
