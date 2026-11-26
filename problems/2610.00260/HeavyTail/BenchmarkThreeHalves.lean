import HeavyTail.EffectiveDimension

/-! Scalar calculations for the shared p=3/2 benchmark. Explicitly, e≥256
and T≥e^(7/4) suffice for domination of the trace/confidence transients and
absence of saturation. The inverse-budget identities also give the stated
small-error ranges. Model-level constants are supplied by the main theorem. -/
noncomputable section
namespace HeavyTail

def benchmarkNoise (e : ℝ) : ℝ := e ^ (-(1 / 2 : ℝ))
def benchmarkDelta (e : ℝ) : ℝ := Real.exp (-e)
def benchmarkRate (e t : ℝ) : ℝ := e ^ (-(1 / 6 : ℝ)) * t ^ (-(1 / 3 : ℝ))
def benchmarkHeavy (e t : ℝ) : ℝ := benchmarkNoise e * ((e + confidenceLog (benchmarkDelta e)) / t) ^ (1 / 3 : ℝ)
def benchmarkInverseBudget (e ε r : ℝ) : ℝ := e ^ (-(1 / 2 : ℝ)) * ε ^ (-r)

theorem benchmarkRate_pos {e t : ℝ} (he : 0 < e) (ht : 0 < t) : 0 < benchmarkRate e t := by
  unfold benchmarkRate
  positivity

theorem benchmarkRate_log {e t : ℝ} (he : 0 < e) (ht : 0 < t) :
    Real.log (benchmarkRate e t) = -(1 / 6 : ℝ) * Real.log e - (1 / 3 : ℝ) * Real.log t := by
  unfold benchmarkRate
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow he, Real.log_rpow ht]
  ring

theorem benchmark_dimension {e : ℝ} (he : 0 < e) : momentDimension 1 (benchmarkNoise e) = e := by
  unfold momentDimension benchmarkNoise
  rw [← Real.rpow_mul_natCast he.le]
  norm_num
  rw [Real.rpow_neg_one]
  simp

theorem benchmark_confidence (e : ℝ) : confidenceLog (benchmarkDelta e) = e + Real.log 3 := by
  unfold confidenceLog benchmarkDelta
  rw [Real.log_div (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem benchmark_confidence_bounds {e : ℝ} (he : 2 ≤ e) :
    e ≤ confidenceLog (benchmarkDelta e) ∧ confidenceLog (benchmarkDelta e) ≤ 2 * e := by
  rw [benchmark_confidence]
  have h0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h1 : Real.log 3 ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at hh
    exact hh
  constructor <;> linarith

theorem benchmark_delta_valid {e : ℝ} (he : 16 ≤ e) :
    0 < benchmarkDelta e ∧ benchmarkDelta e < 1 / 10 := by
  refine ⟨Real.exp_pos _, ?_⟩
  have hexp : (10 : ℝ) < Real.exp e := by linarith [Real.add_one_le_exp e]
  unfold benchmarkDelta
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 10) hexp

theorem benchmark_budget_ge_dimension {e t : ℝ} (he : 1 ≤ e)
    (ht : e ^ (7 / 4 : ℝ) ≤ t) : e ≤ t := by
  apply le_trans _ ht
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le he
    (by norm_num : (1 : ℝ) ≤ 7 / 4)

theorem benchmark_trace_le {e t : ℝ} (he : 0 < e) (het : e ≤ t) :
    1 / Real.sqrt t ≤ benchmarkRate e t := by
  have ht : 0 < t := he.trans_le het
  apply (Real.log_le_log_iff (by positivity) (benchmarkRate_pos he ht)).mp
  rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_sqrt ht.le,
    benchmarkRate_log he ht]
  have hh := Real.log_le_log he het
  linarith

theorem benchmark_transient_le {e t : ℝ} (he : 0 < e)
    (hbudget : e ^ (7 / 4 : ℝ) ≤ t) : e / t ≤ benchmarkRate e t := by
  have ht : 0 < t := (Real.rpow_pos_of_pos he _).trans_le hbudget
  apply (Real.log_le_log_iff (div_pos he ht) (benchmarkRate_pos he ht)).mp
  rw [Real.log_div he.ne' ht.ne', benchmarkRate_log he ht]
  have hh := Real.log_le_log (Real.rpow_pos_of_pos he (7 / 4 : ℝ)) hbudget
  rw [Real.log_rpow he] at hh
  linarith

theorem benchmarkRate_le_budget_edge {e t : ℝ} (he : 0 < e)
    (hbudget : e ^ (7 / 4 : ℝ) ≤ t) : benchmarkRate e t ≤ e ^ (-(3 / 4 : ℝ)) := by
  have ht : 0 < t := (Real.rpow_pos_of_pos he _).trans_le hbudget
  apply (Real.log_le_log_iff (benchmarkRate_pos he ht) (Real.rpow_pos_of_pos he _)).mp
  rw [benchmarkRate_log he ht, Real.log_rpow he]
  have hh := Real.log_le_log (Real.rpow_pos_of_pos he (7 / 4 : ℝ)) hbudget
  rw [Real.log_rpow he] at hh
  linarith

theorem benchmark_noise_power {e t c : ℝ} (he : 0 < e) (ht : 0 < t) (hc : 0 < c) :
    benchmarkNoise e * (c * e / t) ^ (1 / 3 : ℝ) = c ^ (1 / 3 : ℝ) * benchmarkRate e t := by
  have hn : 0 < benchmarkNoise e := Real.rpow_pos_of_pos he _
  have hr := benchmarkRate_pos he ht
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  rw [Real.log_mul hn.ne' (by positivity), Real.log_rpow (by positivity),
    Real.log_div (by positivity) ht.ne', Real.log_mul hc.ne' he.ne',
    Real.log_mul (by positivity) (benchmarkRate_pos he ht).ne',
    Real.log_rpow hc, benchmarkRate_log he ht]
  rw [benchmarkNoise, Real.log_rpow he]
  ring

theorem benchmarkHeavy_bounds {e t : ℝ} (he : 2 ≤ e) (ht : 0 < t) :
    benchmarkRate e t ≤ benchmarkHeavy e t ∧ benchmarkHeavy e t ≤ 3 * benchmarkRate e t := by
  have he0 : 0 < e := by linarith
  have hn : 0 < benchmarkNoise e := Real.rpow_pos_of_pos he0 _
  have hb := benchmark_confidence_bounds he
  have hell : 0 ≤ confidenceLog (benchmarkDelta e) := he0.le.trans hb.1
  have hratio1 : e / t ≤ (e + confidenceLog (benchmarkDelta e)) / t := by gcongr; linarith
  have hratio2 : (e + confidenceLog (benchmarkDelta e)) / t ≤ 3 * e / t := by gcongr; linarith
  have hlow := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (div_pos he0 ht).le hratio1 (by norm_num : (0 : ℝ) ≤ 1 / 3)) hn.le
  have hhigh := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity : 0 ≤ (e + confidenceLog (benchmarkDelta e)) / t)
      hratio2 (by norm_num : (0 : ℝ) ≤ 1 / 3)) hn.le
  have hloid := benchmark_noise_power he0 ht (by norm_num : (0 : ℝ) < 1)
  have hhiid := benchmark_noise_power he0 ht (by norm_num : (0 : ℝ) < 3)
  simp only [one_mul, Real.one_rpow] at hloid
  have hthree : (3 : ℝ) ^ (1 / 3 : ℝ) ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) (by norm_num : (1 / 3 : ℝ) ≤ 1)
  constructor
  · simpa only [hloid, benchmarkHeavy] using hlow
  · change benchmarkHeavy e t ≤ _
    apply hhigh.trans
    rw [hhiid]
    exact mul_le_mul_of_nonneg_right hthree (benchmarkRate_pos he0 ht).le

theorem benchmark_statistical_identity {e : ℝ} (he : 0 < e) (T : ℕ) :
    statisticalAmplitude 1 (benchmarkNoise e) (3 / 2) (benchmarkDelta e) T =
      1 / Real.sqrt T + benchmarkHeavy e T := by
  have hd := benchmark_dimension he
  unfold momentDimension at hd
  unfold statisticalAmplitude benchmarkHeavy
  rw [hd]
  norm_num only [show (1 - 1 / (3 / 2) : ℝ) = 1 / 3 by norm_num]
  rfl

theorem benchmark_amplitudes {e : ℝ} (he : 256 ≤ e) {T : ℕ}
    (hbudget : e ^ (7 / 4 : ℝ) ≤ (T : ℝ)) :
    benchmarkRate e T ≤ statisticalAmplitude 1 (benchmarkNoise e) (3 / 2) (benchmarkDelta e) T ∧
    optimizationAmplitude 1 1 (benchmarkNoise e) (3 / 2) (benchmarkDelta e) T ≤ 7 * benchmarkRate e T := by
  have he0 : 0 < e := by linarith
  have het := benchmark_budget_ge_dimension (by linarith : 1 ≤ e) hbudget
  have ht : (0 : ℝ) < T := he0.trans_le het
  have htrace := benchmark_trace_le he0 het
  have htransient := benchmark_transient_le he0 hbudget
  have hheavy := benchmarkHeavy_bounds (by linarith : 2 ≤ e) ht
  have hconf := (benchmark_confidence_bounds (by linarith : 2 ≤ e)).2
  have hconfT := div_le_div_of_nonneg_right hconf ht.le
  constructor
  · rw [benchmark_statistical_identity he0]
    linarith [show 0 ≤ 1 / Real.sqrt (T : ℝ) by positivity]
  · unfold optimizationAmplitude
    rw [benchmark_statistical_identity he0]
    norm_num
    have heq : 2 * e / (T : ℝ) = 2 * (e / (T : ℝ)) := by ring
    rw [heq] at hconfT
    simp only [one_div] at htrace
    linarith

theorem benchmark_unsaturated {e : ℝ} (he : 256 ≤ e) {T : ℕ}
    (hbudget : e ^ (7 / 4 : ℝ) ≤ (T : ℝ)) :
    7 * benchmarkRate e T ≤ 1 := by
  have he1 : 1 ≤ e := by linarith
  have he0 : 0 < e := by linarith
  have hb := benchmarkRate_le_budget_edge he0 hbudget
  have hp : e ^ (-(3 / 4 : ℝ)) ≤ e ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le he1 (by norm_num)
  have hsqrt : (16 : ℝ) ≤ Real.sqrt e := by
    have hh := Real.sqrt_le_sqrt he
    norm_num at hh
    exact hh
  have hi : e ^ (-(1 / 2 : ℝ)) ≤ 1 / 16 := by
    rw [Real.rpow_neg he0.le, ← Real.sqrt_eq_rpow, one_div]
    exact inv_anti₀ (by norm_num : (0 : ℝ) < 16) hsqrt
  linarith

theorem benchmark_convex_envelope (e t : ℝ) : envelope 0 1 (benchmarkRate e t) = benchmarkRate e t := by
  rw [envelope_zero_curvature, one_mul]

theorem benchmark_strong_envelope {e : ℝ} (he : 256 ≤ e) {T : ℕ}
    (hbudget : e ^ (7 / 4 : ℝ) ≤ (T : ℝ)) :
    envelope 1 1 (benchmarkRate e T) =
      e ^ (-(1 / 3 : ℝ)) * (T : ℝ) ^ (-(2 / 3 : ℝ)) / 2 := by
  have he0 : 0 < e := by linarith
  have ht : (0 : ℝ) < T := (Real.rpow_pos_of_pos he0 _).trans_le hbudget
  have hsmall := benchmark_unsaturated he hbudget
  have hr := (benchmarkRate_pos he0 ht).le
  rw [envelope_quadratic (by norm_num : (0 : ℝ) < 1) (by norm_num; linarith)]
  unfold benchmarkRate
  rw [mul_pow, ← Real.rpow_mul_natCast he0.le, ← Real.rpow_mul_natCast ht.le]
  norm_num

theorem benchmark_inverse_budget_log {e ε r : ℝ} (he : 0 < e) (hε : 0 < ε) :
    Real.log (benchmarkInverseBudget e ε r) = -(1 / 2 : ℝ) * Real.log e - r * Real.log ε := by
  unfold benchmarkInverseBudget
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow he, Real.log_rpow hε]
  ring

theorem benchmark_convex_error_range {e ε : ℝ} (he : 0 < e) (hε : 0 < ε) :
    e ^ (7 / 4 : ℝ) ≤ benchmarkInverseBudget e ε 3 ↔ ε ≤ e ^ (-(3 / 4 : ℝ)) := by
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos he _)
      (by unfold benchmarkInverseBudget; positivity),
    ← Real.log_le_log_iff hε (Real.rpow_pos_of_pos he _),
    benchmark_inverse_budget_log he hε, Real.log_rpow he, Real.log_rpow he]
  constructor <;> intro h <;> linarith

theorem benchmark_strong_error_range {e ε : ℝ} (he : 0 < e) (hε : 0 < ε) :
    e ^ (7 / 4 : ℝ) ≤ benchmarkInverseBudget e ε (3 / 2) ↔ ε ≤ e ^ (-(3 / 2 : ℝ)) := by
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos he _)
      (by unfold benchmarkInverseBudget; positivity),
    ← Real.log_le_log_iff hε (Real.rpow_pos_of_pos he _),
    benchmark_inverse_budget_log he hε, Real.log_rpow he, Real.log_rpow he]
  constructor <;> intro h <;> linarith

theorem benchmarkRate_at_inverse_budget {e ε : ℝ} (he : 0 < e) (hε : 0 < ε) (r : ℝ) :
    benchmarkRate e (benchmarkInverseBudget e ε r) = ε ^ (r / 3) := by
  have ht : 0 < benchmarkInverseBudget e ε r := by unfold benchmarkInverseBudget; positivity
  apply Real.log_injOn_pos (benchmarkRate_pos he ht) (Real.rpow_pos_of_pos hε _)
  rw [benchmarkRate_log he ht, benchmark_inverse_budget_log he hε, Real.log_rpow hε]
  ring

theorem benchmark_convex_inverse_budget {e ε : ℝ} (he : 0 < e) (hε : 0 < ε) :
    benchmarkRate e (benchmarkInverseBudget e ε 3) = ε := by
  rw [benchmarkRate_at_inverse_budget he hε]
  norm_num

theorem benchmark_strong_inverse_budget {e ε : ℝ} (he : 0 < e) (hε : 0 < ε) :
    (benchmarkRate e (benchmarkInverseBudget e ε (3 / 2))) ^ 2 / 2 = ε / 2 := by
  rw [benchmarkRate_at_inverse_budget he hε, ← Real.rpow_mul_natCast hε.le]
  norm_num

end HeavyTail
