import HeavyTail.MainLower

/-! The explicit common rejection threshold from `eq:tau-choice` and its
deterministic comparison with the source all-budget upper amplitude. -/

namespace HeavyTail
noncomputable section

def commonThreshold (G L s p : ℝ) (T : ℕ) : ℝ :=
  128 * max (4 * G + L) (L * ((T : ℝ) / (L ^ 2 / s ^ 2)) ^ (1 / p))

def fixedThresholdAmplitude (G L s p δ τ : ℝ) (T : ℕ) : ℝ :=
  (G + Real.sqrt (L ^ p * τ ^ (2 - p))) / Real.sqrt T +
    G * confidenceLog δ / T + s * (confidenceLog δ / T) ^ (1 - 1 / p) +
      s * (L / τ) ^ (p - 1)

def optimizationAmplitude (G L s p δ : ℝ) (T : ℕ) : ℝ :=
  G / Real.sqrt T + G * confidenceLog δ / T + statisticalAmplitude L s p δ T

theorem commonThreshold_admissible {G L s p : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L) (T : ℕ) :
    64 * (4 * G + L) ≤ commonThreshold G L s p T := by
  unfold commonThreshold
  have h := le_max_left (4 * G + L) (L * ((T : ℝ) / (L ^ 2 / s ^ 2)) ^ (1 / p))
  nlinarith

theorem balanced_trace_identity {L s p t : ℝ} (hL : 0 < L) (hs : 0 < s)
    (hp : 0 < p) (ht : 0 < t) :
    Real.sqrt (L ^ p * (L * (t / (L ^ 2 / s ^ 2)) ^ (1 / p)) ^ (2 - p)) / Real.sqrt t =
      s * ((L ^ 2 / s ^ 2) / t) ^ (1 - 1 / p) := by
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hL,
    Real.log_rpow (by positivity), Real.log_mul hL.ne' (by positivity),
    Real.log_rpow (by positivity), Real.log_div ht.ne' (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_sqrt ht.le, Real.log_mul hs.ne' (by positivity),
    Real.log_rpow (by positivity), Real.log_div (by positivity) ht.ne',
    Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  field_simp [hp.ne']
  <;> ring

theorem balanced_bias_identity {L s p t : ℝ} (hL : 0 < L) (hs : 0 < s)
    (hp : 0 < p) (ht : 0 < t) :
    s * (L / (L * (t / (L ^ 2 / s ^ 2)) ^ (1 / p))) ^ (p - 1) =
      s * ((L ^ 2 / s ^ 2) / t) ^ (1 - 1 / p) := by
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  rw [Real.log_mul hs.ne' (by positivity), Real.log_rpow (by positivity),
    Real.log_div hL.ne' (by positivity), Real.log_mul hL.ne' (by positivity),
    Real.log_rpow (by positivity), Real.log_div ht.ne' (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul hs.ne' (by positivity), Real.log_rpow (by positivity),
    Real.log_div (by positivity) ht.ne', Real.log_div (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  field_simp [hp.ne']
  <;> ring

theorem inflated_trace_le {L B p : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    Real.sqrt (L ^ p * (128 * B) ^ (2 - p)) ≤ 128 * Real.sqrt (L ^ p * B ^ (2 - p)) := by
  have he : 0 ≤ 2 - p := by linarith
  have hf : (128 : ℝ) ^ (2 - p) ≤ (128 : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 128) (by linarith : 2 - p ≤ (2 : ℝ))
  rw [Real.mul_rpow (by norm_num) hB]
  calc
    _ ≤ Real.sqrt ((128 : ℝ) ^ 2 * (L ^ p * B ^ (2 - p))) := by
      apply Real.sqrt_le_sqrt
      have hm := mul_le_mul_of_nonneg_right hf
        (mul_nonneg (Real.rpow_nonneg hL p) (Real.rpow_nonneg hB (2 - p)))
      nlinarith
    _ = 128 * Real.sqrt (L ^ p * B ^ (2 - p)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

theorem trace_at_baseline_le {G L p : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    Real.sqrt (L ^ p * (4 * G + L) ^ (2 - p)) ≤ 4 * G + L := by
  have hB : 0 ≤ 4 * G + L := by positivity
  have hBpow : L ^ p ≤ (4 * G + L) ^ p := Real.rpow_le_rpow hL (by linarith) (by linarith)
  have hprod : (4 * G + L) ^ p * (4 * G + L) ^ (2 - p) = (4 * G + L) ^ 2 := by
    rw [← Real.rpow_add' hB (by linarith : p + (2 - p) ≠ 0)]
    convert Real.rpow_two (4 * G + L) using 1 <;> ring
  apply (Real.sqrt_le_left hB).mpr
  rw [← hprod]
  exact mul_le_mul_of_nonneg_right hBpow (Real.rpow_nonneg hB _)

theorem commonThreshold_trace_bound (θ : OracleParameters) (hT : 0 < θ.T) :
    Real.sqrt (θ.L ^ θ.p * (commonThreshold θ.G θ.L θ.s θ.p θ.T) ^ (2 - θ.p)) /
        Real.sqrt θ.T ≤
      128 * (4 * θ.G + θ.L) / Real.sqrt θ.T +
        128 * MaskedLower.heavyCoefficient θ.L θ.s θ.p θ.T := by
  let C := θ.L * ((θ.T : ℝ) / (θ.L ^ 2 / θ.s ^ 2)) ^ (1 / θ.p)
  have hG := θ.G_pos
  have hs := θ.s_pos
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hTr : (0 : ℝ) < θ.T := Nat.cast_pos.mpr hT
  have hC : 0 < C := by dsimp [C]; positivity
  have hheavy : 0 ≤ MaskedLower.heavyCoefficient θ.L θ.s θ.p θ.T := by
    unfold MaskedLower.heavyCoefficient
    exact mul_nonneg θ.s_pos.le (Real.rpow_nonneg (by positivity) _)
  unfold commonThreshold
  change Real.sqrt (θ.L ^ θ.p * (128 * max (4 * θ.G + θ.L) C) ^ (2 - θ.p)) / _ ≤ _
  by_cases hmax : C ≤ 4 * θ.G + θ.L
  · rw [max_eq_left hmax]
    have hi := (inflated_trace_le hL.le (by positivity : 0 ≤ 4 * θ.G + θ.L)
      θ.p_gt_one.le θ.p_le_two).trans
        (mul_le_mul_of_nonneg_left (trace_at_baseline_le θ.G_pos.le hL.le
          θ.p_gt_one.le θ.p_le_two) (by norm_num))
    exact (div_le_div_of_nonneg_right hi (Real.sqrt_nonneg _)).trans (by nlinarith)
  · rw [max_eq_right (le_of_not_ge hmax)]
    have hi := div_le_div_of_nonneg_right (inflated_trace_le hL.le hC.le θ.p_gt_one.le θ.p_le_two)
      (Real.sqrt_nonneg (θ.T : ℝ))
    have he : 128 * Real.sqrt (θ.L ^ θ.p * C ^ (2 - θ.p)) / Real.sqrt θ.T =
        128 * MaskedLower.heavyCoefficient θ.L θ.s θ.p θ.T := by
      rw [mul_div_assoc]
      exact congrArg (fun x : ℝ => 128 * x)
        (balanced_trace_identity hL θ.s_pos (by linarith only [θ.p_gt_one]) hTr)
    rw [he] at hi
    exact hi.trans (le_add_of_nonneg_left (by positivity))

theorem commonThreshold_bias_bound (θ : OracleParameters) (hT : 0 < θ.T) :
    θ.s * (θ.L / commonThreshold θ.G θ.L θ.s θ.p θ.T) ^ (θ.p - 1) ≤
      MaskedLower.heavyCoefficient θ.L θ.s θ.p θ.T := by
  let C := θ.L * ((θ.T : ℝ) / (θ.L ^ 2 / θ.s ^ 2)) ^ (1 / θ.p)
  have hs := θ.s_pos
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have hTr : (0 : ℝ) < θ.T := Nat.cast_pos.mpr hT
  have hC : 0 < C := by dsimp [C]; positivity
  have hCτ : C ≤ commonThreshold θ.G θ.L θ.s θ.p θ.T := by
    unfold commonThreshold
    change C ≤ 128 * max (4 * θ.G + θ.L) C
    have h := le_max_right (4 * θ.G + θ.L) C
    nlinarith
  have hquot := div_le_div_of_nonneg_left hL.le hC hCτ
  have hτ : 0 < commonThreshold θ.G θ.L θ.s θ.p θ.T := hC.trans_le hCτ
  have hp := Real.rpow_le_rpow (div_nonneg hL.le hτ.le)
    hquot (by linarith only [θ.p_gt_one] : 0 ≤ θ.p - 1)
  have hm := mul_le_mul_of_nonneg_left hp θ.s_pos.le
  exact hm.trans_eq (balanced_bias_identity hL θ.s_pos (by linarith only [θ.p_gt_one]) hTr)

theorem commonThreshold_amplitude_bound (θ : OracleParameters) (hT : 0 < θ.T) :
    fixedThresholdAmplitude θ.G θ.L θ.s θ.p θ.δ
      (commonThreshold θ.G θ.L θ.s θ.p θ.T) θ.T ≤
      1024 * optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ θ.T := by
  let U := θ.s * (((θ.L ^ 2 / θ.s ^ 2) + confidenceLog θ.δ) / θ.T) ^ (1 - 1 / θ.p)
  have hq := MaskedLower.heavyExponent_range θ.p_gt_one θ.p_le_two
  have hG := θ.G_pos
  have hs := θ.s_pos
  have hlog := confidenceLog_pos θ.δ_pos θ.δ_lt_tenth
  have hL : 0 < θ.L := θ.s_pos.trans_le θ.s_le_L
  have htrace := commonThreshold_trace_bound θ hT
  have hbias := commonThreshold_bias_bound θ hT
  have hheavy : MaskedLower.heavyCoefficient θ.L θ.s θ.p θ.T ≤ U := by
    apply mul_le_mul_of_nonneg_left _ θ.s_pos.le
    apply Real.rpow_le_rpow (by positivity) _ hq.1
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    linarith
  have hconf : θ.s * (confidenceLog θ.δ / θ.T) ^ (1 - 1 / θ.p) ≤ U := by
    apply mul_le_mul_of_nonneg_left _ θ.s_pos.le
    apply Real.rpow_le_rpow (by positivity) _ hq.1
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have he : 0 ≤ θ.L ^ 2 / θ.s ^ 2 := by positivity
    linarith
  have hU : 0 ≤ U := mul_nonneg θ.s_pos.le (Real.rpow_nonneg (by positivity) _)
  have hGtrace : 0 ≤ θ.G / Real.sqrt θ.T := by positivity
  have hLtrace : 0 ≤ θ.L / Real.sqrt θ.T := by positivity
  have hconfBudget : 0 ≤ θ.G * confidenceLog θ.δ / θ.T := by positivity
  unfold fixedThresholdAmplitude optimizationAmplitude statisticalAmplitude
  change (θ.G + Real.sqrt _) / Real.sqrt θ.T + θ.G * confidenceLog θ.δ / θ.T +
    θ.s * (confidenceLog θ.δ / θ.T) ^ (1 - 1 / θ.p) +
    θ.s * (θ.L / commonThreshold θ.G θ.L θ.s θ.p θ.T) ^ (θ.p - 1) ≤
      1024 * (θ.G / Real.sqrt θ.T + θ.G * confidenceLog θ.δ / θ.T + (θ.L / Real.sqrt θ.T + U))
  rw [add_div]
  have heq : 128 * (4 * θ.G + θ.L) / Real.sqrt θ.T =
      512 * (θ.G / Real.sqrt θ.T) + 128 * (θ.L / Real.sqrt θ.T) := by ring
  rw [heq] at htrace
  linarith

end
end HeavyTail
