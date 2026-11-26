import NoisyZO.BetaFourProjectedAlgorithm

/-!
# Randomized weighted-iterate output law

Instead of requiring a joint path-space construction merely to return a
weighted point, the algorithm may independently choose iterate `k` with
probability proportional to `k + 1`.  Its expected objective gap is exactly
the weighted marginal-law quantity already controlled by the SGD telescope.
-/

open MeasureTheory
open scoped BigOperators Gradient NNReal ENNReal

namespace NoisyZO

noncomputable section

/-- Probability weight proportional to `k + 1` among `0, ..., n - 1`. -/
def betaFourOutputWeight (n k : ℕ) : ℝ≥0 :=
  ⟨2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1)), by positivity⟩

@[simp]
theorem betaFourOutputWeight_coe (n k : ℕ) :
    (betaFourOutputWeight n k : ℝ) =
      2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1)) := rfl

private lemma sum_range_succ_cast_output (n : ℕ) :
    ∑ k ∈ Finset.range n, (k + 1 : ℝ) =
      (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The iterate-selection weights sum to one for a positive horizon. -/
theorem betaFourOutputWeight_sum_one (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range n, betaFourOutputWeight n k = 1 := by
  apply NNReal.eq
  push_cast
  simp only [betaFourOutputWeight_coe]
  calc
    ∑ k ∈ Finset.range n,
        2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1)) =
        (2 / ((n : ℝ) * (n + 1))) *
          ∑ k ∈ Finset.range n, (k + 1 : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = 1 := by
      rw [sum_range_succ_cast_output]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn0, hn1]

/-- Mixture of recursive marginal laws obtained by selecting an iterate with
the manuscript's linearly increasing weights. -/
def betaFourOutputLaw {d : ℕ} (hd : 0 < d)
    (xnext : ℕ → Point d → FourQuerySample d → Point d) (n : ℕ) :
    Measure (Point d) :=
  ∑ k ∈ Finset.range n,
    betaFourOutputWeight n k • betaFourStateLaw hd xnext k

/-- The weighted iterate mixture is a probability measure. -/
theorem betaFourOutputLaw_isProbability {d : ℕ} (hd : 0 < d)
    (xnext : ℕ → Point d → FourQuerySample d → Point d)
    (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (betaFourOutputLaw hd xnext n) := by
  refine ⟨?_⟩
  rw [betaFourOutputLaw]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply]
  change ∑ k ∈ Finset.range n,
      (betaFourOutputWeight n k : ℝ≥0∞) *
        (betaFourStateLaw hd xnext k) Set.univ = 1
  have huniv : ∀ k, (betaFourStateLaw hd xnext k) Set.univ = 1 := by
    intro k
    let _ : IsProbabilityMeasure (betaFourStateLaw hd xnext k) :=
      betaFourStateLaw_isProbability hd xnext k
    exact measure_univ
  have hweights := congrArg (fun q : ℝ≥0 ↦ (q : ℝ≥0∞))
    (betaFourOutputWeight_sum_one n hn)
  calc
    ∑ k ∈ Finset.range n,
        (betaFourOutputWeight n k : ℝ≥0∞) *
          (betaFourStateLaw hd xnext k) Set.univ =
        ∑ k ∈ Finset.range n,
          (betaFourOutputWeight n k : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [huniv k, mul_one]
    _ = 1 := by simpa using hweights

/-- Objective gaps are integrable under every recursively generated state
law whose transitions remain in the unit ball. -/
theorem NormalizedObjective.betaFourStateLaw_gap_integrable
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d)
    (xnext : ℕ → Point d → FourQuerySample d → Point d)
    (hnextContinuous : ∀ t, Continuous (fun p : Point d × FourQuerySample d ↦
      xnext t p.1 p.2))
    (hnextBall : ∀ t x z, ‖xnext t x z‖ ≤ 1)
    (t : ℕ) :
    Integrable (fun x ↦ F.f x - F.f F.minimizer)
      (betaFourStateLaw hd xnext t) := by
  let _ : IsProbabilityMeasure (betaFourStateLaw hd xnext t) :=
    betaFourStateLaw_isProbability hd xnext t
  have hmeas : AEStronglyMeasurable (fun x ↦ F.f x - F.f F.minimizer)
      (betaFourStateLaw hd xnext t) :=
    (F.smooth.continuous.sub continuous_const).aestronglyMeasurable
  apply (integrable_const (18 : ℝ)).mono' hmeas
  filter_upwards [betaFourStateLaw_mem_unitBall hd xnext
    hnextContinuous hnextBall t] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (F.gap_nonneg x)]
  exact F.gap_le_eighteen_of_norm_le hx

/-- Expected loss under the randomized output law is exactly the weighted
expected-iterate gap used by the telescope. -/
theorem NormalizedObjective.integral_gap_betaFourOutputLaw
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d)
    (xnext : ℕ → Point d → FourQuerySample d → Point d)
    (hnextContinuous : ∀ t, Continuous (fun p : Point d × FourQuerySample d ↦
      xnext t p.1 p.2))
    (hnextBall : ∀ t x z, ‖xnext t x z‖ ≤ 1)
    (n : ℕ) :
    (∫ x, F.f x - F.f F.minimizer ∂betaFourOutputLaw hd xnext n) =
      betaFourWeightedLawGap F hd xnext n := by
  rw [betaFourOutputLaw]
  have hInt : ∀ k ∈ Finset.range n,
      Integrable (fun x ↦ F.f x - F.f F.minimizer)
        (betaFourOutputWeight n k • betaFourStateLaw hd xnext k) := by
    intro k _hk
    exact (F.betaFourStateLaw_gap_integrable hd xnext
      hnextContinuous hnextBall k).smul_measure (by simp)
  rw [integral_finsetSum_measure hInt]
  simp only [integral_smul_nnreal_measure]
  unfold betaFourWeightedLawGap
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  change
    (2 * (k + 1 : ℝ) / ((n : ℝ) * (n + 1))) *
        betaFourLawGap F hd xnext k =
      (2 / ((n : ℝ) * (n + 1))) *
        ((k + 1 : ℝ) * betaFourLawGap F hd xnext k)
  ring

/-- The explicit projected algorithm's randomized output law attains the
balanced `β = 4` expected-loss rate. -/
theorem NormalizedObjective.betaFourProjectedOutputLaw_balanced_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (hd : 0 < d)
    (n : ℕ) (hn : 0 < n) (hbudget : d ^ 2 ≤ n + 1) :
    (∫ x, F.f x - F.f F.minimizer
      ∂betaFourOutputLaw hd
        (betaFourProjectedTransition F (betaFourBandwidth d n)) n) ≤
      (131905 / 144 : ℝ) *
        ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ (3 / 4 : ℝ) := by
  rw [F.integral_gap_betaFourOutputLaw hd
    (betaFourProjectedTransition F (betaFourBandwidth d n))
    (fun t ↦ continuous_betaFourProjectedTransition F _ t)
    (fun t x z ↦ norm_betaFourProjectedTransition_le_one F _ t x z) n]
  exact F.betaFourProjectedStateLaw_balanced_rate hbeta hd n hn hbudget

/-- Explicit output distribution under a raw-query budget.  Above the
dimension threshold it runs `T / 4` projected four-query iterations and
selects a weighted iterate; below the threshold it returns zero. -/
def betaFourProjectedBudgetOutputLaw
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (T : ℕ) : Measure (Point d) :=
  if 8 * d ^ 2 ≤ T then
    betaFourOutputLaw hd
      (betaFourProjectedTransition F (betaFourBandwidth d (T / 4))) (T / 4)
  else Measure.dirac 0

/-- The raw-budget output distribution is always a probability measure for a
positive budget. -/
theorem betaFourProjectedBudgetOutputLaw_isProbability
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hd : 0 < d) (T : ℕ) (hT : 0 < T) :
    IsProbabilityMeasure (betaFourProjectedBudgetOutputLaw F hd T) := by
  unfold betaFourProjectedBudgetOutputLaw
  split_ifs with hlarge
  · apply betaFourOutputLaw_isProbability
    have hd2 : 0 < d ^ 2 := pow_pos hd _
    omega
  · infer_instance

/-- In the high-budget branch, the explicit output law obeys the four-raw-call
rate after replacing the iteration count by `T`. -/
theorem NormalizedObjective.betaFourProjectedOutputLaw_raw_budget_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (hd : 0 < d)
    (T : ℕ) (hlarge : 8 * d ^ 2 ≤ T) :
    (∫ x, F.f x - F.f F.minimizer
      ∂betaFourOutputLaw hd
        (betaFourProjectedTransition F (betaFourBandwidth d (T / 4))) (T / 4)) ≤
      (131905 / 144 : ℝ) * 8 ^ (3 / 4 : ℝ) *
        ((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ) := by
  let n : ℕ := T / 4
  have hn : 0 < n := by
    dsimp only [n]
    have hd2 : 0 < d ^ 2 := pow_pos hd _
    omega
  have hbudget : d ^ 2 ≤ n + 1 := by
    dsimp only [n]
    have hfour : 4 * d ^ 2 ≤ T := by omega
    have hdiv : d ^ 2 ≤ T / 4 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
      simpa [Nat.mul_comm] using hfour
    omega
  have hmain := F.betaFourProjectedOutputLaw_balanced_rate hbeta hd n hn hbudget
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1R : 0 < (n + 1 : ℝ) := by positivity
  have hTR : 0 < (T : ℝ) := by
    have hd1 : 1 ≤ d := hd
    exact_mod_cast (show 0 < T by omega)
  have hratioSucc :
      (d : ℝ) ^ 2 / (n + 1 : ℝ) ≤ (d : ℝ) ^ 2 / n := by
    apply (div_le_div_iff₀ hn1R hnR).2
    nlinarith [sq_nonneg (d : ℝ)]
  have hscheduled : (d : ℝ) ^ 2 / n ≤ 8 * (d : ℝ) ^ 2 / T := by
    have hraw := dimension_ratio_scheduled_le (d := d) (T := T) (q := 4)
      (by norm_num) (by
        have hd2 : 0 < d ^ 2 := pow_pos hd _
        omega)
    norm_num at hraw
    simpa only [n] using hraw
  have hratio :
      (d : ℝ) ^ 2 / (n + 1 : ℝ) ≤ 8 * ((d : ℝ) ^ 2 / T) := by
    calc
      (d : ℝ) ^ 2 / (n + 1 : ℝ) ≤ (d : ℝ) ^ 2 / n := hratioSucc
      _ ≤ 8 * (d : ℝ) ^ 2 / T := hscheduled
      _ = 8 * ((d : ℝ) ^ 2 / T) := by ring
  have hpow := Real.rpow_le_rpow
    (by positivity : 0 ≤ (d : ℝ) ^ 2 / (n + 1 : ℝ)) hratio
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
  calc
    (∫ x, F.f x - F.f F.minimizer
      ∂betaFourOutputLaw hd
        (betaFourProjectedTransition F (betaFourBandwidth d (T / 4))) (T / 4)) ≤
        (131905 / 144 : ℝ) *
          ((d : ℝ) ^ 2 / (n + 1 : ℝ)) ^ (3 / 4 : ℝ) := by
      simpa only [n] using hmain
    _ ≤ (131905 / 144 : ℝ) *
        (8 * ((d : ℝ) ^ 2 / T)) ^ (3 / 4 : ℝ) := by
      gcongr
    _ = (131905 / 144 : ℝ) * 8 ^ (3 / 4 : ℝ) *
        ((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring

/-- Complete saturated raw-query guarantee for the explicit randomized
algorithm output law. -/
theorem NormalizedObjective.betaFourProjectedBudgetOutputLaw_saturated_rate
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (hbeta : o.beta = 4) (hd : 0 < d)
    (T : ℕ) (hT : 0 < T) :
    (∫ x, F.f x - F.f F.minimizer
      ∂betaFourProjectedBudgetOutputLaw F hd T) ≤
      (131905 / 144 : ℝ) * 8 ^ (3 / 4 : ℝ) *
        min 1 (((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ)) := by
  by_cases hlarge : 8 * d ^ 2 ≤ T
  · have hmain := F.betaFourProjectedOutputLaw_raw_budget_rate
      hbeta hd T hlarge
    have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
    have hlargeR : (8 : ℝ) * (d : ℝ) ^ 2 ≤ T := by exact_mod_cast hlarge
    have hratioOne : (d : ℝ) ^ 2 / T ≤ 1 := by
      rw [div_le_one hTR]
      nlinarith [sq_nonneg (d : ℝ)]
    have hpowOne :
        ((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ) ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by positivity : 0 ≤ (d : ℝ) ^ 2 / T)
          hratioOne (by norm_num : (0 : ℝ) ≤ 3 / 4)
    rw [betaFourProjectedBudgetOutputLaw, if_pos hlarge, min_eq_right hpowOne]
    exact hmain
  · have hsmall : T < 8 * d ^ 2 := Nat.lt_of_not_ge hlarge
    have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
    have hsmallR : (T : ℝ) < 8 * (d : ℝ) ^ 2 := by exact_mod_cast hsmall
    have hratioLower : (1 / 8 : ℝ) < (d : ℝ) ^ 2 / T := by
      rw [lt_div_iff₀ hTR]
      nlinarith
    have hpowLower :
        (1 / 8 : ℝ) ^ (3 / 4 : ℝ) ≤
          ((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hratioLower.le (by norm_num)
    have hpowFloor :
        (1 / 8 : ℝ) ^ (3 / 4 : ℝ) ≤
          min 1 (((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ)) := by
      apply le_min
      · simpa only [Real.one_rpow] using
          Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 8)
            (by norm_num : (1 / 8 : ℝ) ≤ 1)
            (by norm_num : (0 : ℝ) ≤ 3 / 4)
      · exact hpowLower
    have hcancel :
        (8 : ℝ) ^ (3 / 4 : ℝ) *
          (1 / 8 : ℝ) ^ (3 / 4 : ℝ) = 1 := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]
      norm_num
    rw [betaFourProjectedBudgetOutputLaw, if_neg hlarge, integral_dirac]
    calc
      F.f 0 - F.f F.minimizer ≤ 9 := F.zero_gap_le_nine
      _ ≤ (131905 / 144 : ℝ) := by norm_num
      _ = (131905 / 144 : ℝ) * 8 ^ (3 / 4 : ℝ) *
          (1 / 8 : ℝ) ^ (3 / 4 : ℝ) := by
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ (131905 / 144 : ℝ) * 8 ^ (3 / 4 : ℝ) *
          min 1 (((d : ℝ) ^ 2 / T) ^ (3 / 4 : ℝ)) := by
        gcongr

end

end NoisyZO
