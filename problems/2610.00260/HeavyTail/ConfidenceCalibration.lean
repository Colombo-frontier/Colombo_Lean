import HeavyTail.ConfidenceAmplitude

/-! Explicit confidence tuning for the erasure construction, including its
finite-budget exponential probability and the uniform envelope constant. -/
noncomputable section
set_option maxHeartbeats 800000
namespace HeavyTail

def confidenceLog (δ : ℝ) : ℝ := Real.log (3 / δ)
def erasureLog (δ : ℝ) : ℝ := Real.log (1 / (4 * δ))

theorem erasureLog_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 10) :
    0 < erasureLog δ := by
  apply Real.log_pos
  apply (one_lt_div (by positivity : 0 < 4 * δ)).mpr
  linarith

theorem confidenceLog_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 10) :
    0 < confidenceLog δ := by
  apply Real.log_pos
  apply (one_lt_div hδ).mpr
  linarith

theorem confidenceLog_le_four_erasureLog {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1 / 10) :
    confidenceLog δ ≤ 4 * erasureLog δ := by
  let x := 1 / (4 * δ)
  have hx : (5 / 2 : ℝ) ≤ x := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * δ)).mpr
    linarith
  have hx0 : 0 < x := by positivity
  have hcube : (12 : ℝ) ≤ x ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2) hx 3
    norm_num at h
    linarith
  have hl : Real.log 12 ≤ 3 * Real.log x := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by norm_num) hcube
  have hsplit : 3 / δ = 12 * x := by dsimp [x]; ring
  unfold confidenceLog erasureLog
  rw [hsplit, Real.log_mul (by norm_num) hx0.ne']
  change Real.log 12 + Real.log x ≤ 4 * Real.log x
  linarith

theorem heavyTailExponent_mem {p : ℝ} (hp : 1 < p) :
    0 ≤ 1 - 1 / p ∧ 1 - 1 / p ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hdiv : 1 / p ≤ 1 := (div_le_one hp0).mpr hp.le
  have hpos : 0 ≤ 1 / p := by positivity
  constructor <;> linarith

theorem confidenceAmplitude_rate {G s p δ : ℝ} {T : ℕ}
    (hG : 0 ≤ G) (hs : 0 ≤ s) (hp : 1 < p)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 10) (hT : 0 < T) :
    (1 / 8 : ℝ) * min G (s * (confidenceLog δ / T) ^ (1 - 1 / p)) ≤
      confidenceAmplitude G s p (erasureLog δ / T) := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hb := erasureLog_pos hδ hδ1
  have hl := confidenceLog_pos hδ hδ1
  obtain ⟨hq0, hq1⟩ := heavyTailExponent_mem hp
  have hbase : confidenceLog δ / T ≤ 4 * (erasureLog δ / T) := by
    have h := div_le_div_of_nonneg_right (confidenceLog_le_four_erasureLog hδ hδ1) hTr.le
    simpa only [mul_div_assoc] using h
  have hpow : (confidenceLog δ / T) ^ (1 - 1 / p) ≤
      4 * (erasureLog δ / T) ^ (1 - 1 / p) := by
    calc
      _ ≤ (4 * (erasureLog δ / T)) ^ (1 - 1 / p) :=
        Real.rpow_le_rpow (by positivity) hbase hq0
      _ = (4 : ℝ) ^ (1 - 1 / p) * (erasureLog δ / T) ^ (1 - 1 / p) :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) hq1) (Real.rpow_nonneg (by positivity) _)
  have ht : 0 ≤ min G (s * (confidenceLog δ / T) ^ (1 - 1 / p)) := by positivity
  unfold confidenceAmplitude
  apply le_min
  · have h := min_le_left G (s * (confidenceLog δ / T) ^ (1 - 1 / p))
    nlinarith only [h, ht]
  · calc
      _ ≤ (1 / 8 : ℝ) * (s * (confidenceLog δ / T) ^ (1 - 1 / p)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ ≤ (s / 2) * (erasureLog δ / T) ^ (1 - 1 / p) := by
        have h := mul_le_mul_of_nonneg_left hpow hs
        nlinarith only [h]

theorem confidenceAmplitude_envelope {μ D G s p δ : ℝ} {T : ℕ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hG : 0 ≤ G) (hs : 0 ≤ s) (hp : 1 < p)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 10) (hT : 0 < T) :
    (1 / 64 : ℝ) * envelope μ D (min G (s * (confidenceLog δ / T) ^ (1 - 1 / p))) ≤
      envelope μ D (confidenceAmplitude G s p (erasureLog δ / T)) := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hl := confidenceLog_pos hδ hδ1
  have ha : 0 ≤ min G (s * (confidenceLog δ / T) ^ (1 - 1 / p)) := by positivity
  have hscale := envelope_scale_lower hμ hD ha (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hnum : (1 / 8 : ℝ) ^ 2 = 1 / 64 := by norm_num
  rw [hnum] at hscale
  exact hscale.trans (envelope_mono hμ hD (mul_nonneg (by norm_num) ha)
    (confidenceAmplitude_rate hG hs hp hδ hδ1 hT))

theorem confidence_erasure_probability {δ : ℝ} {T : ℕ}
    (hδ : 0 < δ) (hT : 0 < T) :
    (Real.exp (-(erasureLog δ / T))) ^ T = 4 * δ := by
  have hT0 : (T : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hT)
  rw [← Real.rpow_natCast, ← Real.exp_mul]
  have he : -(erasureLog δ / T) * T = -erasureLog δ := by field_simp
  rw [he, Real.exp_neg, erasureLog, Real.exp_log (by positivity)]
  field_simp

end HeavyTail
