import LowRank.GaussianStartingBlockBound
import LowRank.SchattenExactRecovery

/-! A numerical 1/20 failure bound for an oversampled Gaussian starting
block, including the zero-tail case. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem iidMatrixLaw_startingBlock_factor_bad_le {a d k s : ℕ}
    (M : Matrix (Fin a) (Fin d) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (hs : 2 * k + 2 ≤ s) :
    (iidMatrixLaw d s 1) {U |
      1600 * (s : ℝ) * frobeniusSq M < frobeniusSq ((M * U) * gramRightInverse (Vᵀ * U))} ≤ 1 / 20 := by
  by_cases hz : frobeniusSq M = 0
  · have hM := (frobeniusSq_eq_zero_iff M).mp hz
    subst M
    simp [frobeniusSq]
  · have hF : 0 < frobeniusSq M := lt_of_le_of_ne (frobeniusSq_nonneg M) (Ne.symm hz)
    have hsn : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
    let E : ℝ := (s : ℝ) * frobeniusSq M
    have hE : 0 < E := mul_pos hsn hF
    have hR : 0 < 40 * E := mul_pos (by norm_num) hE
    have h := iidMatrixLaw_startingBlock_factor_tail M V hV (by omega : k + 2 ≤ s)
      hR (by norm_num : (0 : ℝ) < 40)
    have hfirst : ENNReal.ofReal E / ENNReal.ofReal (40 * E) = 1 / 40 := by
      rw [← ENNReal.ofReal_div_of_pos hR]
      have heq : E / (40 * E) = 1 / 40 := by field_simp; ring
      rw [heq, ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    have hdim : 2 * (k : ℝ) + 2 ≤ s := by exact_mod_cast hs
    have hden : 0 < (s : ℝ) - k - 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hmean : (k : ℝ) / ((s : ℝ) - k - 1) ≤ 1 := by
      apply (div_le_iff₀ hden).mpr
      linarith
    have hsecond : ENNReal.ofReal ((k : ℝ) / ((s : ℝ) - k - 1)) / ENNReal.ofReal 40 ≤ 1 / 40 := by
      simpa using ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hmean) (ENNReal.ofReal 40)
    have heq : 40 * E * 40 = 1600 * (s : ℝ) * frobeniusSq M := by dsimp [E]; ring
    rw [heq] at h
    change _ ≤ ENNReal.ofReal E / ENNReal.ofReal (40 * E) + _ at h
    rw [hfirst] at h
    calc
      _ ≤ _ := h
      _ ≤ (1 / 40 : ℝ≥0∞) + 1 / 40 := add_le_add_left hsecond _
      _ = _ := by
        have h40 : (1 / 40 : ℝ≥0∞) = ENNReal.ofReal (1 / 40) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]
          norm_num
        have h20 : (1 / 20 : ℝ≥0∞) = ENNReal.ofReal (1 / 20) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]
          norm_num
        rw [h40, h20, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        congr 1
        norm_num

end
end LowRank
