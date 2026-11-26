import HeavyTail.SampleComplexity
import HeavyTail.BenchmarkSampleCosts
import HeavyTail.BenchmarkParameters

/-! The p=3/2 benchmark for the actual infimum over raw-call budgets,
including zero-query exclusion through the general sample-complexity theorem. -/

noncomputable section
open scoped ENNReal
namespace HeavyTail

def benchmarkSampleLowerConstant : ℝ := sampleLowerConstant (3 / 2) / 4

def benchmarkSampleUpperConstant : ℝ := 8 * sampleUpperConstant (3 / 2)

theorem benchmark_sample_constants :
    0 < benchmarkSampleLowerConstant ∧ 0 < benchmarkSampleUpperConstant ∧
    benchmarkSampleLowerConstant ≤ sampleLowerConstant (3 / 2) / 2 ∧
    benchmarkSampleLowerConstant ≤ 1 / 4 := by
  have hp := sampleLowerConstant_pos (3 / 2)
  have hu := sampleUpperConstant_pos (3 / 2)
  have hh : sampleLowerConstant (3 / 2) ≤ 1 / 294912 := min_le_left _ _
  unfold benchmarkSampleLowerConstant benchmarkSampleUpperConstant
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> linarith

theorem benchmark_convex_sample_complexity {e ε : ℝ} {d : ℕ}
    (he : 256 ≤ e) (hε : 0 < ε) (hdim : Nat.ceil e ≤ d)
    (hsmall : ε ≤ benchmarkSampleLowerConstant * e ^ (-(3 / 4 : ℝ))) :
    ENNReal.ofReal (benchmarkSampleLowerConstant * benchmarkInverseBudget e ε 3) ≤
      sampleComplexity (HardSpace d) (benchmarkParameters e 0 0 he (by norm_num)) ε ∧
    sampleComplexity (HardSpace d) (benchmarkParameters e 0 0 he (by norm_num)) ε ≤
      ENNReal.ofReal (benchmarkSampleUpperConstant * benchmarkInverseBudget e ε 3) := by
  have hc := benchmark_sample_constants
  have hp := sampleLowerConstant_pos (3 / 2)
  have hedge : e ^ (-(3 / 4 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith : 1 ≤ e) (by norm_num)
  have hεc : ε ≤ benchmarkSampleLowerConstant :=
    hsmall.trans ((mul_le_mul_of_nonneg_left hedge hc.1.le).trans_eq (mul_one _))
  have hs : ε ≤ sampleLowerConstant (3 / 2) * envelope 0 1 1 := by
    rw [envelope_zero_curvature]
    norm_num
    linarith [hc.2.2.1]
  have ha : ε ≤ e ^ (-(3 / 4 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right (show benchmarkSampleLowerConstant ≤ 1 by linarith [hc.2.2.2])
      (Real.rpow_nonneg (by linarith : 0 ≤ e) (-(3 / 4 : ℝ)))
    exact hsmall.trans (by simpa only [one_mul] using hh)
  have hcost := benchmark_sample_cost_bounds (by linarith : 2 ≤ e) hε ha
  have hm := sample_complexity_bounds (benchmarkParameters e 0 0 he (by norm_num)) hε hs
    (by simpa only [benchmarkParameters_dimension] using hdim)
  have hinv : envelopeInverse 0 1 ε = ε := by simp [envelopeInverse]
  change ENNReal.ofReal (sampleLowerConstant (3 / 2) * sampleLowerCost 1 (benchmarkNoise e)
      (3 / 2) (benchmarkDelta e) (envelopeInverse 0 1 ε)) ≤ _ ∧
    _ ≤ ENNReal.ofReal (sampleUpperConstant (3 / 2) * sampleUpperCost 1 1 (benchmarkNoise e)
      (3 / 2) (benchmarkDelta e) (envelopeInverse 0 1 ε)) at hm
  rw [hinv] at hm
  have hB := (benchmarkInverseBudget_pos (r := 3) (by linarith : 0 < e) hε).le
  constructor
  · apply (ENNReal.ofReal_le_ofReal ?_).trans hm.1
    calc
      _ ≤ sampleLowerConstant (3 / 2) * benchmarkInverseBudget e ε 3 :=
        mul_le_mul_of_nonneg_right (by linarith [hc.2.2.1]) hB
      _ ≤ _ := mul_le_mul_of_nonneg_left hcost.1 hp.le
  · apply hm.2.trans (ENNReal.ofReal_le_ofReal ?_)
    have hh := mul_le_mul_of_nonneg_left hcost.2 (sampleUpperConstant_pos (3 / 2)).le
    unfold benchmarkSampleUpperConstant
    nlinarith only [hh]

theorem benchmark_strong_sample_complexity {e ε : ℝ} {d : ℕ}
    (he : 256 ≤ e) (hε : 0 < ε) (hdim : Nat.ceil e ≤ d)
    (hsmall : ε ≤ benchmarkSampleLowerConstant * e ^ (-(3 / 2 : ℝ))) :
    ENNReal.ofReal (benchmarkSampleLowerConstant * benchmarkInverseBudget e ε (3 / 2)) ≤
      sampleComplexity (HardSpace d) (benchmarkParameters e 1 0 he (by norm_num)) ε ∧
    sampleComplexity (HardSpace d) (benchmarkParameters e 1 0 he (by norm_num)) ε ≤
      ENNReal.ofReal (benchmarkSampleUpperConstant * benchmarkInverseBudget e ε (3 / 2)) := by
  have hc := benchmark_sample_constants
  have hp := sampleLowerConstant_pos (3 / 2)
  have he0 : 0 < e := by linarith
  have hedge : e ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith : 1 ≤ e) (by norm_num)
  have hεc : ε ≤ benchmarkSampleLowerConstant :=
    hsmall.trans ((mul_le_mul_of_nonneg_left hedge hc.1.le).trans_eq (mul_one _))
  have hεhalf : ε ≤ 1 / 2 := by linarith [hc.2.2.2]
  have henv : envelope 1 1 1 = 1 / 2 := by
    rw [envelope_quadratic (by norm_num : (0 : ℝ) < 1) (by norm_num)]
    norm_num
  have hs : ε ≤ sampleLowerConstant (3 / 2) * envelope 1 1 1 := by
    rw [henv]
    linarith [hc.2.2.1]
  have hinv : envelopeInverse 1 1 ε = Real.sqrt (2 * ε) := by
    norm_num [envelopeInverse, hεhalf]
  have ha : Real.sqrt (2 * ε) ≤ e ^ (-(3 / 4 : ℝ)) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hpow : (e ^ (-(3 / 4 : ℝ))) ^ 2 = e ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_mul_natCast he0.le]
        norm_num
      rw [hpow]
      have hh := mul_le_mul_of_nonneg_right hc.2.2.2
        (Real.rpow_nonneg he0.le (-(3 / 2 : ℝ)))
      linarith
  have hcost := benchmark_sample_cost_bounds (by linarith : 2 ≤ e)
    (by positivity : 0 < Real.sqrt (2 * ε)) ha
  have hB := benchmark_sqrt_inverse_budget_bounds he0 hε
  have hm := sample_complexity_bounds (benchmarkParameters e 1 0 he (by norm_num)) hε hs
    (by simpa only [benchmarkParameters_dimension] using hdim)
  change ENNReal.ofReal (sampleLowerConstant (3 / 2) * sampleLowerCost 1 (benchmarkNoise e)
      (3 / 2) (benchmarkDelta e) (envelopeInverse 1 1 ε)) ≤ _ ∧
    _ ≤ ENNReal.ofReal (sampleUpperConstant (3 / 2) * sampleUpperCost 1 1 (benchmarkNoise e)
      (3 / 2) (benchmarkDelta e) (envelopeInverse 1 1 ε)) at hm
  rw [hinv] at hm
  constructor
  · apply (ENNReal.ofReal_le_ofReal ?_).trans hm.1
    have hh := mul_le_mul_of_nonneg_left (hB.1.trans hcost.1) hp.le
    unfold benchmarkSampleLowerConstant
    nlinarith only [hh]
  · apply hm.2.trans (ENNReal.ofReal_le_ofReal ?_)
    have hh := mul_le_mul_of_nonneg_left
      (hcost.2.trans (mul_le_mul_of_nonneg_left hB.2 (by norm_num : (0 : ℝ) ≤ 8)))
      (sampleUpperConstant_pos (3 / 2)).le
    unfold benchmarkSampleUpperConstant
    nlinarith only [hh]

/-- The small-error ranges force the corresponding raw-call budgets into
the same regime as the benchmark error theorem. -/
theorem benchmark_scaled_inverse_budget_range {e ε c b r : ℝ}
    (he : 0 < e) (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1)
    (hr : 1 ≤ r) (hbr : b * r = 9 / 4)
    (hsmall : ε ≤ c * e ^ (-b)) :
    e ^ (7 / 4 : ℝ) ≤ c * benchmarkInverseBudget e ε r := by
  have hB := benchmarkInverseBudget_pos (r := r) he hε
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos he _) (mul_pos hc hB)).mp
  rw [Real.log_rpow he, Real.log_mul hc.ne' hB.ne', benchmark_inverse_budget_log he hε]
  have hh := Real.log_le_log hε hsmall
  rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos he _).ne', Real.log_rpow he] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (zero_le_one.trans hr)
  have hcL : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hmulc := mul_le_mul_of_nonpos_right hr hcL
  have heq : r * (b * Real.log e) = (9 / 4 : ℝ) * Real.log e := by
    rw [← mul_assoc, mul_comm r b, hbr]
  nlinarith only [hmul, hmulc, heq]

theorem benchmark_convex_sample_budget_threshold {e ε : ℝ} {d : ℕ}
    (he : 256 ≤ e) (hε : 0 < ε) (hdim : Nat.ceil e ≤ d)
    (hsmall : ε ≤ benchmarkSampleLowerConstant * e ^ (-(3 / 4 : ℝ))) :
    ENNReal.ofReal (e ^ (7 / 4 : ℝ)) ≤
      sampleComplexity (HardSpace d) (benchmarkParameters e 0 0 he (by norm_num)) ε := by
  have hc := benchmark_sample_constants
  have hscalar := benchmark_scaled_inverse_budget_range (by linarith : 0 < e) hε hc.1
    (by linarith [hc.2.2.2] : benchmarkSampleLowerConstant ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 3) (by norm_num : (3 / 4 : ℝ) * 3 = 9 / 4) hsmall
  exact (ENNReal.ofReal_le_ofReal hscalar).trans
    (benchmark_convex_sample_complexity he hε hdim hsmall).1

theorem benchmark_strong_sample_budget_threshold {e ε : ℝ} {d : ℕ}
    (he : 256 ≤ e) (hε : 0 < ε) (hdim : Nat.ceil e ≤ d)
    (hsmall : ε ≤ benchmarkSampleLowerConstant * e ^ (-(3 / 2 : ℝ))) :
    ENNReal.ofReal (e ^ (7 / 4 : ℝ)) ≤
      sampleComplexity (HardSpace d) (benchmarkParameters e 1 0 he (by norm_num)) ε := by
  have hc := benchmark_sample_constants
  have hscalar := benchmark_scaled_inverse_budget_range (by linarith : 0 < e) hε hc.1
    (by linarith [hc.2.2.2] : benchmarkSampleLowerConstant ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) * (3 / 2) = 9 / 4) hsmall
  exact (ENNReal.ofReal_le_ofReal hscalar).trans
    (benchmark_strong_sample_complexity he hε hdim hsmall).1

end HeavyTail
