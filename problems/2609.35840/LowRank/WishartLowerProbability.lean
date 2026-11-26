import LowRank.WishartMomentConstants
import LowRank.WishartLowerTailInterface

/-! The uniform lower positive spectral probability for normalized rectangular
Gaussian inputs, with a fixed numerical constant and every positive codimension. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem normalized_inverseGram_tail {d s k : ℕ} (hsize : s + 1 + k = d) (hk : 0 < k)
    (i : Fin (s + 1)) :
    (iidMatrixLaw d (s + 1) (d : NNReal)⁻¹)
      {X | wishartInverseThreshold d k < inverseGramEigenvalue X i} ≤ ENNReal.ofReal (1 / 40) := by
  have hd : 0 < d := by omega
  have hs : s + 1 ≤ d := by omega
  have hv : (d : NNReal)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hd.ne')
  have hres : d - s = k + 1 := by omega
  have hR := wishartInverseThreshold_pos hd hk
  by_cases hk4 : 4 ≤ k
  · have hqm : 2 * (k / 4) < k + 1 := by omega
    have hqmR : 2 * ((k / 4 : ℕ) : ℝ) < (k + 1 : ℕ) := by exact_mod_cast hqm
    have ha : 0 < ((d - s : ℕ) : ℝ) / 2 - ((k / 4 : ℕ) : ℝ) := by rw [hres]; linarith
    have h := inverseGram_tail_le_ofReal hs hv i (by positivity) ha hR
    rw [hres, Real.rpow_natCast] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (inverseGramMomentBound_large_ratio
      (by omega : 0 < s + 1) hsize hk4))
  · by_cases hk1 : k = 1
    · subst k
      have ha : 0 < ((d - s : ℕ) : ℝ) / 2 - (1 / 2) := by rw [hres]; norm_num
      have h := inverseGram_tail_le_ofReal hs hv i (by norm_num : (0 : ℝ) ≤ 1 / 2) ha hR
      rw [hres] at h
      exact h.trans (ENNReal.ofReal_le_ofReal (inverseGramMomentBound_half_ratio
        (by omega : 0 < s + 1) hs))
    · have ha : 0 < ((d - s : ℕ) : ℝ) / 2 - (1 : ℝ) := by
        rw [hres]
        have hkR : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
        push_cast
        linarith
      have h := inverseGram_tail_le_ofReal hs hv i (by norm_num : (0 : ℝ) ≤ 1) ha hR
      rw [hres, Real.rpow_one] at h
      exact h.trans (ENNReal.ofReal_le_ofReal (inverseGramMomentBound_small_ratio
        (by omega : 0 < s + 1) hsize (by omega) (by omega)))

theorem wishartInverseThreshold_inv {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    (wishartInverseThreshold d k)⁻¹ = (1 / 1000000 : ℝ) * ((k : ℝ) / d) ^ 2 := by
  unfold wishartInverseThreshold
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

theorem gaussianMatrixLaw_wishart_lower_tail {d k : ℕ} (hk : 0 < k) (hkd : k < d) :
    (gaussianMatrixLaw d (d - k)).real
      (wishartLowerSpectralEvent d (d - k) (1 / 1000000) k)ᶜ ≤ 1 / 40 := by
  have hd : 0 < d := by omega
  cases hcols : d - k with
  | zero => omega
  | succ s =>
    have hsize : s + 1 + k = d := by omega
    have hR := wishartInverseThreshold_pos hd hk
    have htail := normalized_inverseGram_tail hsize hk (Fin.last s)
    have hbad := (wishart_lower_bad_le_inverseGram_tail
      (iidMatrixLaw d (s + 1) (d : NNReal)⁻¹) hR).trans htail
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
    norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 40)] at hreal
    have heq : (wishartLowerSpectralEvent d (s + 1) (1 / 1000000) k)ᶜ =
        {X | ¬LoewnerLE ((wishartInverseThreshold d k)⁻¹ • (1 - leftKernelProjector X))
          (wishart X)} := by
      ext X
      simp only [wishartLowerSpectralEvent, Set.mem_compl_iff, Set.mem_setOf_eq,
        wishartInverseThreshold_inv hd hk]
    rw [heq]
    exact hreal

theorem gaussianMatrixLaw_wishart_spectral_probability {d k : ℕ} (hk : 0 < k) (hkd : k < d) :
    (gaussianMatrixLaw d (d - k)).real
      (wishartSpectralEvent d (d - k) 8192 (1 / 1000000) k)ᶜ ≤ 1 / 20 :=
  wishartSpectralEvent_probability_of_lower_tail (by omega) (Nat.sub_le _ _)
    (gaussianMatrixLaw_wishart_lower_tail hk hkd)

end
end LowRank
