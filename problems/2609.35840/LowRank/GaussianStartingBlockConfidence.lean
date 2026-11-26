import LowRank.GaussianStartingBlockConstant

/-! Adjustable confidence for the Gaussian starting-block product. This
bound can be shared across many spectral targets by a finite union bound. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem iidMatrixLaw_startingBlock_confidence_le {a d k s : ℕ}
    (M : Matrix (Fin a) (Fin d) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (hs : 2 * k + 2 ≤ s) {q : ℝ} (hq : 0 < q) :
    (iidMatrixLaw d s 1) {U |
      q ^ 2 * (s : ℝ) * frobeniusSq M < frobeniusSq ((M * U) * gramRightInverse (Vᵀ * U))} ≤
        ENNReal.ofReal (2 / q) := by
  by_cases hz : frobeniusSq M = 0
  · have hM := (frobeniusSq_eq_zero_iff M).mp hz
    subst M
    simp [frobeniusSq]
  · have hF : 0 < frobeniusSq M := lt_of_le_of_ne (frobeniusSq_nonneg M) (Ne.symm hz)
    have hsn : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
    let E : ℝ := (s : ℝ) * frobeniusSq M
    have hE : 0 < E := mul_pos hsn hF
    have hR : 0 < q * E := mul_pos hq hE
    have h := iidMatrixLaw_startingBlock_factor_tail M V hV (by omega : k + 2 ≤ s) hR hq
    have hfirst : ENNReal.ofReal E / ENNReal.ofReal (q * E) = ENNReal.ofReal (1 / q) := by
      rw [← ENNReal.ofReal_div_of_pos hR]
      congr 1
      field_simp
      ring
    have hdim : 2 * (k : ℝ) + 2 ≤ s := by exact_mod_cast hs
    have hden : 0 < (s : ℝ) - k - 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hmean : (k : ℝ) / ((s : ℝ) - k - 1) ≤ 1 := by
      apply (div_le_iff₀ hden).mpr
      linarith
    have hsecond : ENNReal.ofReal ((k : ℝ) / ((s : ℝ) - k - 1)) / ENNReal.ofReal q ≤
        ENNReal.ofReal (1 / q) := by
      rw [ENNReal.ofReal_div_of_pos hq]
      exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hmean) _
    have heq : q * E * q = q ^ 2 * (s : ℝ) * frobeniusSq M := by dsimp [E]; ring
    rw [heq] at h
    change _ ≤ ENNReal.ofReal E / ENNReal.ofReal (q * E) + _ at h
    rw [hfirst] at h
    calc
      _ ≤ _ := h
      _ ≤ ENNReal.ofReal (1 / q) + ENNReal.ofReal (1 / q) := add_le_add_left hsecond _
      _ = ENNReal.ofReal (2 / q) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end
end LowRank
