import FullJet.RandomEpochOutput

namespace FullJet

noncomputable def higherErrorCoefficient (p : ℕ) (L : ℝ) (m : ℕ) : ℝ :=
  (p : ℝ) * L * (m : ℝ) ^ (p - 1)

noncomputable def gradientNoiseCoefficient (p : ℕ) (L : ℝ) (m B : ℕ) : ℝ :=
  Real.sqrt m * (L * (m : ℝ) ^ (p - 1)) / Real.sqrt B

noncomputable def upperErrorScale (p : ℕ) (L : ℝ) (m B : ℕ) : ℝ :=
  L + higherErrorCoefficient p L m + gradientNoiseCoefficient p L m B

noncomputable def upperModelScale (p : ℕ) (L : ℝ) (m B : ℕ) : ℝ :=
  128 * ((p + 1).factorial : ℝ) * upperErrorScale p L m B

noncomputable def upperRadius (p : ℕ) (L ε : ℝ) (m B : ℕ) : ℝ :=
  (ε / (32 * upperModelScale p L m B)) ^ (1 / (p : ℝ))

/-- A whole number of complete snapshot periods; no partial final period is needed. -/
noncomputable def upperEpochCount (p : ℕ) (Δ L ε : ℝ) (m B : ℕ) : ℕ :=
  ⌈Δ / ((m : ℝ) * upperErrorScale p L m B * upperRadius p L ε m B ^ (p + 1))⌉₊

theorem higherErrorCoefficient_nonneg (p : ℕ) (L : ℝ) (m : ℕ) (hL : 0 ≤ L) :
    0 ≤ higherErrorCoefficient p L m := by unfold higherErrorCoefficient; positivity

theorem gradientNoiseCoefficient_nonneg (p : ℕ) (L : ℝ) (m B : ℕ) (hL : 0 ≤ L) :
    0 ≤ gradientNoiseCoefficient p L m B := by unfold gradientNoiseCoefficient; positivity

theorem upperErrorScale_pos (p : ℕ) (L : ℝ) (m B : ℕ) (hL : 0 < L) :
    0 < upperErrorScale p L m B := by
  have hd := higherErrorCoefficient_nonneg p L m hL.le
  have hs := gradientNoiseCoefficient_nonneg p L m B hL.le
  unfold upperErrorScale
  linarith

theorem upperModelScale_pos (p : ℕ) (L : ℝ) (m B : ℕ) (hL : 0 < L) :
    0 < upperModelScale p L m B := by
  have hs := upperErrorScale_pos p L m B hL
  unfold upperModelScale
  positivity

theorem upperRadius_pos (p : ℕ) (L ε : ℝ) (m B : ℕ) (hL : 0 < L) (hε : 0 < ε) :
    0 < upperRadius p L ε m B := by
  have hM := upperModelScale_pos p L m B hL
  unfold upperRadius
  exact Real.rpow_pos_of_pos (by positivity) _

theorem upperRadius_pow (p : ℕ) (hp : 0 < p) (L ε : ℝ) (m B : ℕ)
    (hL : 0 < L) (hε : 0 < ε) :
    upperRadius p L ε m B ^ p = ε / (32 * upperModelScale p L m B) := by
  have hM := upperModelScale_pos p L m B hL
  have hbase : 0 ≤ ε / (32 * upperModelScale p L m B) := by positivity
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [upperRadius, ← Real.rpow_natCast, ← Real.rpow_mul hbase, one_div_mul_cancel hp', Real.rpow_one]

theorem upperRadius_equation (p : ℕ) (hp : 0 < p) (L ε : ℝ) (m B : ℕ)
    (hL : 0 < L) (hε : 0 < ε) :
    32 * upperModelScale p L m B * upperRadius p L ε m B ^ p = ε := by
  rw [upperRadius_pow p hp L ε m B hL hε]
  have hM := upperModelScale_pos p L m B hL
  field_simp

theorem epochNoiseBound_factor (p : ℕ) (hp : 0 < p) (L : ℝ) (m : ℕ) (r : ℝ) (B : ℕ) :
    epochNoiseBound p L m r B = gradientNoiseCoefficient p L m B * r ^ p := by
  have hpow : r ^ (p - 1) * r = r ^ p := by rw [← pow_succ, Nat.sub_add_cancel hp]
  unfold epochNoiseBound gradientNoiseCoefficient
  rw [mul_pow]
  calc
    _ = (Real.sqrt m * (L * (m : ℝ) ^ (p - 1)) / Real.sqrt B) * (r ^ (p - 1) * r) := by ring
    _ = _ := by rw [hpow]

theorem upperEpochCount_pos (p : ℕ) (Δ L ε : ℝ) (m B : ℕ)
    (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) (hm : 0 < m) :
    0 < upperEpochCount p Δ L ε m B := by
  have hs := upperErrorScale_pos p L m B hL
  have hr := upperRadius_pos p L ε m B hL hε
  unfold upperEpochCount
  apply Nat.ceil_pos.mpr
  positivity

theorem upperEpochCount_work (p : ℕ) (Δ L ε : ℝ) (m B : ℕ)
    (hL : 0 < L) (hε : 0 < ε) (hm : 0 < m) :
    Δ ≤ (upperEpochCount p Δ L ε m B : ℝ) * m * upperErrorScale p L m B *
      upperRadius p L ε m B ^ (p + 1) := by
  have hs := upperErrorScale_pos p L m B hL
  have hr := upperRadius_pos p L ε m B hL hε
  have hd : 0 < (m : ℝ) * upperErrorScale p L m B * upperRadius p L ε m B ^ (p + 1) := by positivity
  have hc := (div_le_iff₀ hd).mp (Nat.le_ceil
    (Δ / ((m : ℝ) * upperErrorScale p L m B * upperRadius p L ε m B ^ (p + 1))))
  simpa only [upperEpochCount, mul_assoc] using hc

/-- Rounding the total number of steps up to whole periods costs at most one period. -/
theorem upperEpochCount_steps_le (p : ℕ) (Δ L ε : ℝ) (m B : ℕ)
    (hΔ : 0 ≤ Δ) (hL : 0 < L) (hε : 0 < ε) (hm : 0 < m) :
    (upperEpochCount p Δ L ε m B : ℝ) * m ≤
      Δ / (upperErrorScale p L m B * upperRadius p L ε m B ^ (p + 1)) + m := by
  have hs := upperErrorScale_pos p L m B hL
  have hr := upperRadius_pos p L ε m B hL hε
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one
    (show 0 ≤ Δ / ((m : ℝ) * upperErrorScale p L m B * upperRadius p L ε m B ^ (p + 1)) by positivity)).le
    (show (0 : ℝ) ≤ m by positivity)
  apply hc.trans_eq
  field_simp
  ring

theorem upperModelScale_ge_errorScale (p : ℕ) (L : ℝ) (m B : ℕ) (hL : 0 < L) :
    upperErrorScale p L m B ≤ upperModelScale p L m B := by
  have hs := upperErrorScale_pos p L m B hL
  have hF : (1 : ℝ) ≤ (p + 1).factorial := by exact_mod_cast Nat.factorial_pos (p + 1)
  unfold upperModelScale
  nlinarith [mul_le_mul_of_nonneg_right hF hs.le]

theorem upperModelScale_descent (p : ℕ) (L : ℝ) (m B : ℕ) (hL : 0 < L) :
    64 * upperErrorScale p L m B ≤ upperModelScale p L m B / ((p + 1).factorial : ℝ) - L := by
  have hF : ((p + 1).factorial : ℝ) ≠ 0 := by positivity
  have hs := upperErrorScale_pos p L m B hL
  have hd := higherErrorCoefficient_nonneg p L m hL.le
  have hn := gradientNoiseCoefficient_nonneg p L m B hL.le
  have hS : L ≤ upperErrorScale p L m B := by unfold upperErrorScale; linarith
  have he : upperModelScale p L m B / ((p + 1).factorial : ℝ) = 128 * upperErrorScale p L m B := by
    unfold upperModelScale
    field_simp
    ring
  rw [he]
  linarith

end FullJet
