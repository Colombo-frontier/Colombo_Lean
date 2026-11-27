import Nonsmooth.LocalizationVolumeAccuracy

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem dimension_log_at_least_one (d : ℕ) (hd : 2 ≤ d) :
    1 ≤ (d : ℝ) * Real.log ((d : ℝ) + 1) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : (1 / 2 : ℝ) ≤ Real.log ((d : ℝ) + 1) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
  nlinarith

theorem total_evaluated_localization_query_bound (d : ℕ) (hd : 2 ≤ d) {A c η : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (T : ℕ) (hT : (T : ℝ) ≤ A * (d : ℝ) * Real.log ((d : ℝ) + 1)) :
    ((volumeLocalizationRounds d c η * (T + 1) : ℕ) : ℝ) ≤
      (3 * (A + 2) / c) * (d : ℝ) ^ 2 * Real.log ((d : ℝ) + 1) * Real.log (1 / η) := by
  have hv := dimension_log_at_least_one d hd
  have hT' : ((T + 1 : ℕ) : ℝ) ≤ (A + 1) * (d : ℝ) * Real.log ((d : ℝ) + 1) := by
    push_cast
    nlinarith only [hT, hv]
  have hround : T + 1 ≤ ⌈(A + 1) * (d : ℝ) * Real.log ((d : ℝ) + 1)⌉₊ := by
    exact_mod_cast hT'.trans (Nat.le_ceil _)
  have hmul := Nat.mul_le_mul_left (volumeLocalizationRounds d c η) hround
  have hbound := total_localization_query_bound d hd (by linarith : 0 ≤ A + 1) hc hc1 hη hηhalf
  have hmulR : ((volumeLocalizationRounds d c η * (T + 1) : ℕ) : ℝ) ≤
      ((volumeLocalizationRounds d c η * ⌈(A + 1) * (d : ℝ) * Real.log ((d : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast hmul
  convert! hmulR.trans hbound using 1 <;> ring

end
end Nonsmooth
