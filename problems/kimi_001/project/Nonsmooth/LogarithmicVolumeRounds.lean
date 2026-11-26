import Nonsmooth.VolumeContractionIteration

open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def volumeLocalizationRounds (d : ℕ) (c η : ℝ) : ℕ :=
  ⌈((d : ℝ) * Real.log (1 / η) + 1) / c⌉₊

theorem volumeLocalizationRounds_power_lt (d : ℕ) {c η : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hη : 0 < η) :
    (1 - c) ^ volumeLocalizationRounds d c η < η ^ d := by
  have hq : 0 < 1 - c := sub_pos.mpr hc1
  have hl : Real.log (1 - c) ≤ -c := by
    have h := Real.log_le_sub_one_of_pos hq
    linarith
  have hceil := Nat.le_ceil (((d : ℝ) * Real.log (1 / η) + 1) / c)
  change ((d : ℝ) * Real.log (1 / η) + 1) / c ≤ (volumeLocalizationRounds d c η : ℝ) at hceil
  have hcount := (div_le_iff₀ hc).mp hceil
  have hm := mul_le_mul_of_nonneg_left hl
    (show (0 : ℝ) ≤ volumeLocalizationRounds d c η from Nat.cast_nonneg _)
  have hlog : Real.log (1 / η) = -Real.log η := by rw [one_div, Real.log_inv]
  rw [hlog] at hcount
  apply (Real.log_lt_log_iff (pow_pos hq _) (pow_pos hη d)).mp
  rw [Real.log_pow, Real.log_pow]
  nlinarith only [hcount, hm]

theorem volumeLocalizationRounds_bound (d : ℕ) (hd : 2 ≤ d) {c η : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    (volumeLocalizationRounds d c η : ℝ) ≤ (3 / c) * (d : ℝ) * Real.log (1 / η) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have htwo : (2 : ℝ) ≤ 1 / η := (le_div_iff₀ hη).mpr (by linarith)
  have hlog : (1 / 2 : ℝ) ≤ Real.log (1 / η) := hlog2.trans (Real.log_le_log (by norm_num) htwo)
  let A := (d : ℝ) * Real.log (1 / η)
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (A + 1) / c from div_nonneg (by linarith) hc.le)
  change (volumeLocalizationRounds d c η : ℝ) < (A + 1) / c + 1 at hceil
  have hcount := (lt_div_iff₀ hc).mp
    (show (volumeLocalizationRounds d c η : ℝ) - 1 < (A + 1) / c by linarith)
  have heq : (3 / c) * (d : ℝ) * Real.log (1 / η) = (3 * A) / c := by dsimp [A]; ring
  rw [heq]
  apply (le_div_iff₀ hc).mpr
  nlinarith only [hcount, hA, hc1]

theorem volume_fraction_below_relative_threshold (v : ℕ → ℝ≥0∞) (d : ℕ) {c η : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hη : 0 < η) (hv0 : 0 < v 0) (hvfinite : v 0 < ∞)
    (hstep : ∀ n < volumeLocalizationRounds d c η,
      v (n + 1) + ENNReal.ofReal c * v n ≤ v n) :
    v (volumeLocalizationRounds d c η) < ENNReal.ofReal (η ^ d) * v 0 := by
  have hbound := volume_fraction_iterate v hc.le hc1.le hvfinite (volumeLocalizationRounds d c η) hstep
  have hpow : ENNReal.ofReal (1 - c) ^ volumeLocalizationRounds d c η < ENNReal.ofReal (η ^ d) := by
    rw [← ENNReal.ofReal_pow (sub_nonneg.mpr hc1.le)]
    exact (ENNReal.ofReal_lt_ofReal_iff (pow_pos hη d)).mpr (volumeLocalizationRounds_power_lt d hc hc1 hη)
  have hmul := (ENNReal.mul_lt_mul_iff_left hv0.ne' hvfinite.ne).mpr hpow
  exact hbound.trans_lt hmul

end
end Nonsmooth
