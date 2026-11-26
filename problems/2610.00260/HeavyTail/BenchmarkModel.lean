import HeavyTail.BenchmarkParameters
import HeavyTail.MainTheorem

/-! Actual minimax error benchmark in the full oracle model, with arbitrary
randomized adaptive policies and the paper's almost-sure raw-call budget. -/
noncomputable section
open scoped ENNReal
namespace HeavyTail

theorem benchmark_minimax_envelope {e μ : ℝ} {T d : ℕ}
    (he : 256 ≤ e) (hμ : 0 ≤ μ) (hdim : Nat.ceil e ≤ d)
    (hbudget : e ^ (7 / 4 : ℝ) ≤ (T : ℝ)) :
    ENNReal.ofReal ((1 / 147456 : ℝ) * envelope μ 1 (benchmarkRate e T)) ≤
      atMostCallMinimax (HardSpace d) (benchmarkParameters e μ T he hμ) ∧
    atMostCallMinimax (HardSpace d) (benchmarkParameters e μ T he hμ) ≤
      ENNReal.ofReal (unifiedUpperConstant (3 / 2) * envelope μ 1 (7 * benchmarkRate e T)) := by
  have he0 : 0 < e := by linarith
  have ht : (0 : ℝ) < T := (Real.rpow_pos_of_pos he0 _).trans_le hbudget
  have hT : 0 < T := Nat.cast_pos.mp ht
  have hmain := unified_all_budget (benchmarkParameters e μ T he hμ) hT
    (by simpa only [benchmarkParameters_dimension] using hdim)
  have ha := benchmark_amplitudes he hbudget
  have hsmall := benchmark_unsaturated he hbudget
  have hr := benchmarkRate_pos he0 ht
  have hr1 : benchmarkRate e T ≤ 1 := by linarith
  have hlow := envelope_mono hμ (by norm_num : (0 : ℝ) ≤ 1) hr.le (le_min hr1 ha.1)
  have hα := benchmark_delta_valid (by linarith : 16 ≤ e)
  have hell := (confidenceLog_pos hα.1 hα.2).le
  have hstat : 0 ≤ statisticalAmplitude 1 (benchmarkNoise e) (3 / 2) (benchmarkDelta e) T := hr.le.trans ha.1
  have hopt : 0 ≤ optimizationAmplitude 1 1 (benchmarkNoise e) (3 / 2) (benchmarkDelta e) T := by
    unfold optimizationAmplitude
    positivity
  have hup : envelope μ 1
      (min 1 (optimizationAmplitude 1 1 (benchmarkNoise e) (3 / 2) (benchmarkDelta e) T)) ≤
        envelope μ 1 (7 * benchmarkRate e T) :=
    envelope_mono hμ (by norm_num : (0 : ℝ) ≤ 1)
      (le_min (by norm_num) hopt) ((min_le_right _ _).trans ha.2)
  constructor
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hlow (by norm_num))).trans hmain.1
  · exact hmain.2.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hup (unifiedUpperConstant_pos (3 / 2)).le))

theorem benchmark_convex_minimax_bounds {e : ℝ} {T d : ℕ}
    (he : 256 ≤ e) (hdim : Nat.ceil e ≤ d)
    (hbudget : e ^ (7 / 4 : ℝ) ≤ (T : ℝ)) :
    ENNReal.ofReal ((1 / 147456 : ℝ) * (e ^ (-(1 / 6 : ℝ)) * (T : ℝ) ^ (-(1 / 3 : ℝ)))) ≤
      atMostCallMinimax (HardSpace d) (benchmarkParameters e 0 T he (by norm_num)) ∧
    atMostCallMinimax (HardSpace d) (benchmarkParameters e 0 T he (by norm_num)) ≤
      ENNReal.ofReal ((7 * unifiedUpperConstant (3 / 2)) *
        (e ^ (-(1 / 6 : ℝ)) * (T : ℝ) ^ (-(1 / 3 : ℝ)))) := by
  have h := benchmark_minimax_envelope he (by norm_num : (0 : ℝ) ≤ 0) hdim hbudget
  simpa only [envelope_zero_curvature, one_mul, benchmarkRate, mul_left_comm,
    mul_comm (unifiedUpperConstant (3 / 2)) (7 : ℝ), mul_assoc] using h

theorem benchmark_strong_minimax_bounds {e : ℝ} {T d : ℕ}
    (he : 256 ≤ e) (hdim : Nat.ceil e ≤ d)
    (hbudget : e ^ (7 / 4 : ℝ) ≤ (T : ℝ)) :
    ENNReal.ofReal ((1 / 294912 : ℝ) * (e ^ (-(1 / 3 : ℝ)) * (T : ℝ) ^ (-(2 / 3 : ℝ)))) ≤
      atMostCallMinimax (HardSpace d) (benchmarkParameters e 1 T he (by norm_num)) ∧
    atMostCallMinimax (HardSpace d) (benchmarkParameters e 1 T he (by norm_num)) ≤
      ENNReal.ofReal (((49 / 2 : ℝ) * unifiedUpperConstant (3 / 2)) *
        (e ^ (-(1 / 3 : ℝ)) * (T : ℝ) ^ (-(2 / 3 : ℝ)))) := by
  have h := benchmark_minimax_envelope he (by norm_num : (0 : ℝ) ≤ 1) hdim hbudget
  have hsmall := benchmark_unsaturated he hbudget
  have he0 : 0 < e := by linarith
  have ht : (0 : ℝ) < T := (Real.rpow_pos_of_pos he0 _).trans_le hbudget
  have hr := (benchmarkRate_pos he0 ht).le
  have hlo : envelope 1 1 (benchmarkRate e T) = (benchmarkRate e T) ^ 2 / 2 :=
    by rw [envelope_quadratic (by norm_num : (0 : ℝ) < 1) (by norm_num; linarith)]; norm_num
  have hhi : envelope 1 1 (7 * benchmarkRate e T) = 49 * (benchmarkRate e T) ^ 2 / 2 := by
    rw [envelope_quadratic (by norm_num : (0 : ℝ) < 1) (by simpa using hsmall)]
    ring
  have hsq : (benchmarkRate e T) ^ 2 = e ^ (-(1 / 3 : ℝ)) * (T : ℝ) ^ (-(2 / 3 : ℝ)) := by
    unfold benchmarkRate
    rw [mul_pow, ← Real.rpow_mul_natCast he0.le, ← Real.rpow_mul_natCast ht.le]
    norm_num
  rw [hlo, hhi, hsq] at h
  convert h using 1 <;> congr 1 <;> ring

end HeavyTail
