import HeavyTail.MaskedKernelMoments

/-! Real-power calibration for the one-coordinate revelation oracle. -/

namespace HeavyTail.MaskedLower
noncomputable section

def maskedAmplitude (G L p : ℝ) (k : ℕ) (π : ℝ) : ℝ :=
  min G ((L / (4 * Real.sqrt k)) * ((k : ℝ) * π) ^ (1 - 1 / p))

theorem maskedAmplitude_nonneg {G L p π : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hπ : 0 ≤ π) (k : ℕ) : 0 ≤ maskedAmplitude G L p k π := by
  unfold maskedAmplitude
  positivity

theorem maskedAmplitude_le_G (G L p : ℝ) (k : ℕ) (π : ℝ) :
    maskedAmplitude G L p k π ≤ G := min_le_left _ _

theorem sparse_power_normalization {M r p : ℝ} (hM : 0 ≤ M) (hr : 0 < r) (hp : 0 < p) :
    r * ((M * r ^ (1 - 1 / p)) / r) ^ p = M ^ p := by
  have he : (1 - 1 / p) * p = p - 1 := by field_simp [hp.ne']
  rw [Real.div_rpow (by positivity) hr.le, Real.mul_rpow hM (by positivity),
    ← Real.rpow_mul hr.le, he, Real.rpow_sub_one hr.ne']
  field_simp [hr.ne', (Real.rpow_pos_of_pos hr p).ne']
  ring

theorem sparse_power_budget {M r p a : ℝ} (hM : 0 ≤ M) (hr : 0 < r) (hr1 : r ≤ 1)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hab : a ≤ M * r ^ (1 - 1 / p)) :
    r * (a / r) ^ p ≤ M ^ p ∧ a ^ p ≤ M ^ p := by
  have hp0 : 0 < p := by linarith
  have hq : 0 ≤ 1 - 1 / p := sub_nonneg.mpr ((div_le_one hp0).mpr hp)
  have har : a ≤ M := hab.trans (by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left (Real.rpow_le_one hr.le hr1 hq) hM))
  constructor
  · calc
      _ ≤ r * ((M * r ^ (1 - 1 / p)) / r) ^ p :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hab hr.le) hp0.le) hr.le
      _ = _ := sparse_power_normalization hM hr hp0
  · exact Real.rpow_le_rpow ha har hp0.le

theorem quarter_power_budget {M p : ℝ} (hM : 0 ≤ M) (hp : 1 ≤ p) :
    4 * (M / 4) ^ p ≤ M ^ p := by
  rw [Real.div_rpow hM (by norm_num)]
  have hfour : (4 : ℝ) ≤ (4 : ℝ) ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hp
  have hratio : 4 / (4 : ℝ) ^ p ≤ 1 := (div_le_one (by positivity)).mpr hfour
  have h := mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hM p)
  calc
    4 * (M ^ p / (4 : ℝ) ^ p) = M ^ p * (4 / (4 : ℝ) ^ p) := by ring
    _ ≤ M ^ p := by simpa only [mul_one] using h

end
end HeavyTail.MaskedLower
