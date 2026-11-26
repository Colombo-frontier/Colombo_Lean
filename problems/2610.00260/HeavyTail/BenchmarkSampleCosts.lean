import HeavyTail.SampleComplexityCosts
import HeavyTail.BenchmarkThreeHalves

/-! Exact sample-cost calculations for the p=3/2 benchmark, retaining the
source error ranges and the square-root inverse in the strongly convex case. -/

noncomputable section
namespace HeavyTail

theorem benchmarkInverseBudget_pos {e ε r : ℝ} (he : 0 < e) (hε : 0 < ε) :
    0 < benchmarkInverseBudget e ε r := by
  unfold benchmarkInverseBudget
  positivity

theorem benchmark_cubic_noise_identity {e a : ℝ} (he : 0 < e) (ha : 0 < a) :
    e * (benchmarkNoise e / a) ^ 3 = benchmarkInverseBudget e a 3 := by
  have hn : 0 < benchmarkNoise e := Real.rpow_pos_of_pos he _
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (benchmarkInverseBudget_pos he ha)
  rw [Real.log_mul he.ne' (by positivity), Real.log_pow, Real.log_div hn.ne' ha.ne',
    benchmark_inverse_budget_log he ha, benchmarkNoise, Real.log_rpow he]
  ring

theorem benchmark_sample_trace_cost {e a : ℝ} (he : 1 ≤ e) (ha : 0 < a)
    (hsmall : a ≤ e ^ (-(3 / 4 : ℝ))) :
    1 / a ^ 2 ≤ benchmarkInverseBudget e a 3 := by
  have he0 : 0 < e := zero_lt_one.trans_le he
  apply (Real.log_le_log_iff (by positivity : 0 < 1 / a ^ 2) (benchmarkInverseBudget_pos he0 ha)).mp
  rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_pow,
    benchmark_inverse_budget_log he0 ha]
  have hh := Real.log_le_log ha hsmall
  rw [Real.log_rpow he0] at hh
  have heL := Real.log_nonneg he
  norm_num
  linarith

theorem benchmark_sample_confidence_cost {e a : ℝ} (he : 0 < e) (ha : 0 < a)
    (hsmall : a ≤ e ^ (-(3 / 4 : ℝ))) :
    e / a ≤ benchmarkInverseBudget e a 3 := by
  apply (Real.log_le_log_iff (div_pos he ha) (benchmarkInverseBudget_pos he ha)).mp
  rw [Real.log_div he.ne' ha.ne', benchmark_inverse_budget_log he ha]
  have hh := Real.log_le_log ha hsmall
  rw [Real.log_rpow he] at hh
  linarith

theorem benchmark_sample_cost_bounds {e a : ℝ} (he : 2 ≤ e) (ha : 0 < a)
    (hsmall : a ≤ e ^ (-(3 / 4 : ℝ))) :
    benchmarkInverseBudget e a 3 ≤ sampleLowerCost 1 (benchmarkNoise e) (3 / 2) (benchmarkDelta e) a ∧
    sampleUpperCost 1 1 (benchmarkNoise e) (3 / 2) (benchmarkDelta e) a ≤
      8 * benchmarkInverseBudget e a 3 := by
  have he0 : 0 < e := by linarith
  have hn : 0 < benchmarkNoise e := Real.rpow_pos_of_pos he0 _
  have hB : 0 < benchmarkInverseBudget e a 3 := benchmarkInverseBudget_pos he0 ha
  have hconf := benchmark_confidence_bounds he
  have hid := benchmark_cubic_noise_identity he0 ha
  have hp0 : 0 ≤ (benchmarkNoise e / a) ^ 3 := by positivity
  have hl : e ≤ e + confidenceLog (benchmarkDelta e) := by linarith
  have hh : e + confidenceLog (benchmarkDelta e) ≤ 3 * e := by linarith
  have hlow := mul_le_mul_of_nonneg_right hl hp0
  rw [hid] at hlow
  have hhigh : (e + confidenceLog (benchmarkDelta e)) * (benchmarkNoise e / a) ^ 3 ≤
      3 * benchmarkInverseBudget e a 3 := by
    calc
      _ ≤ 3 * e * (benchmarkNoise e / a) ^ 3 := mul_le_mul_of_nonneg_right hh hp0
      _ = 3 * benchmarkInverseBudget e a 3 := by rw [mul_assoc, hid]
  have htrace := benchmark_sample_trace_cost (by linarith : 1 ≤ e) ha hsmall
  have hlinear := benchmark_sample_confidence_cost he0 ha hsmall
  have hconfidence : confidenceLog (benchmarkDelta e) / a ≤ 2 * benchmarkInverseBudget e a 3 := by
    apply (div_le_div_of_nonneg_right hconf.2 ha.le).trans
    have h := mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1 <;> ring
  have hbudget := (benchmark_convex_error_range he0 ha).mpr hsmall
  have hone : 1 ≤ benchmarkInverseBudget e a 3 :=
    (Real.one_le_rpow (by linarith : 1 ≤ e) (by norm_num : (0 : ℝ) ≤ 7 / 4)).trans hbudget
  have hd := benchmark_dimension he0
  unfold momentDimension at hd
  have htwo : 2 / a ^ 2 ≤ 2 * benchmarkInverseBudget e a 3 := by
    convert mul_le_mul_of_nonneg_left htrace (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have hpow : (benchmarkNoise e / a) ^ (3 : ℝ) = (benchmarkNoise e / a) ^ (3 : ℕ) :=
    Real.rpow_natCast _ 3
  constructor
  · unfold sampleLowerCost
    rw [hd]
    norm_num [Real.rpow_natCast]
    rw [hpow]
    exact Or.inr hlow
  · unfold sampleUpperCost
    rw [hd]
    norm_num [Real.rpow_natCast]
    rw [hpow]
    calc
      _ ≤ benchmarkInverseBudget e a 3 + 2 * benchmarkInverseBudget e a 3 +
          2 * benchmarkInverseBudget e a 3 + 3 * benchmarkInverseBudget e a 3 :=
        add_le_add (add_le_add (add_le_add hone htwo) hconfidence) hhigh
      _ = 8 * benchmarkInverseBudget e a 3 := by ring

theorem benchmark_sqrt_inverse_budget_identity {e ε : ℝ} (he : 0 < e) (hε : 0 < ε) :
    benchmarkInverseBudget e (Real.sqrt (2 * ε)) 3 =
      (2 : ℝ) ^ (-(3 / 2 : ℝ)) * benchmarkInverseBudget e ε (3 / 2) := by
  have hB : 0 < benchmarkInverseBudget e ε (3 / 2) := benchmarkInverseBudget_pos he hε
  apply Real.log_injOn_pos (benchmarkInverseBudget_pos he (by positivity))
    (by simp only [Set.mem_Ioi]; positivity)
  rw [benchmark_inverse_budget_log he (by positivity), Real.log_sqrt (by positivity),
    Real.log_mul (by norm_num) hε.ne', Real.log_mul (by positivity) (benchmarkInverseBudget_pos he hε).ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 2), benchmark_inverse_budget_log he hε]
  ring

theorem benchmark_sqrt_inverse_budget_bounds {e ε : ℝ} (he : 0 < e) (hε : 0 < ε) :
    (1 / 4 : ℝ) * benchmarkInverseBudget e ε (3 / 2) ≤
        benchmarkInverseBudget e (Real.sqrt (2 * ε)) 3 ∧
    benchmarkInverseBudget e (Real.sqrt (2 * ε)) 3 ≤ benchmarkInverseBudget e ε (3 / 2) := by
  rw [benchmark_sqrt_inverse_budget_identity he hε]
  have hlo : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
    calc
      (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by norm_num [Real.rpow_neg, Real.rpow_two]
      _ ≤ (2 : ℝ) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (-2 : ℝ) ≤ -(3 / 2 : ℝ))
  have hhi : (2 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : -(3 / 2 : ℝ) ≤ 0)
  have hB := (benchmarkInverseBudget_pos (r := 3 / 2) he hε).le
  exact ⟨mul_le_mul_of_nonneg_right hlo hB,
    (mul_le_mul_of_nonneg_right hhi hB).trans_eq (one_mul _)⟩

end HeavyTail
