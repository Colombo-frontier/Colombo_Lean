import NCConcave16991.MainAssembly
import NCConcave16991.UpperAssembly
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Reduction of the headline theorem to the algorithm and hard-instance theorems

This proves the implication between the full oracle-model specifications.
It does not prove either of its two construction hypotheses.
-/

open scoped ENNReal

namespace NCConcave16991

theorem complexityLog_one_le (p : ProblemParameters) (hA : 1 ≤ dimensionlessA p) :
    1 ≤ complexityLog p := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  have hB := dimensionlessB_nonneg p
  have hq : 4 ≤ 2 + (p.n : ℝ) + dimensionlessA p + dimensionlessB p := by linarith
  unfold complexityLog
  apply (Real.le_log_iff_exp_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hq)).2
  have he := Real.exp_one_lt_three
  linarith

private theorem complexity_upper_of_valid_bound {p : ProblemParameters}
    {mode : SmoothnessClass} {budget : ℕ} {b : ℝ}
    (hvalid : ValidBudget p mode budget) (hb : (budget : ℝ) ≤ b) :
    oracleComplexity p mode ≤ ENNReal.ofReal b := by
  apply (oracleComplexity_le_of_valid hvalid).trans
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hb

/-- Once Theorems 3.2 and 3.3 are proved for the actual oracle model, the global
statement of Theorem 3.1 follows, with explicit constants `c/2` and `4C`. -/
theorem theorem31Global_of_theorem32_and_theorem33
    (hupper : Theorem32Specification) (hlower : Theorem33Specification) :
    Theorem31GlobalSpecification := by
  obtain ⟨C, hC, hupper⟩ := hupper
  obtain ⟨A0, c, hA0, hc, hlower⟩ := hlower
  refine ⟨max A0 1, c / 2, 4 * C, ?_, by positivity, by positivity, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right A0 1)
  intro p hthreshold
  have hA : 1 ≤ dimensionlessA p := (le_max_right A0 1).trans hthreshold
  have hA0' : A0 ≤ dimensionlessA p := (le_max_left A0 1).trans hthreshold
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  have hB := dimensionlessB_nonneg p
  have hell := complexityLog_one_le p hA
  obtain ⟨hl1, hl2⟩ := hlower p hA0'
  obtain ⟨havg, hacc⟩ := hupper p
  obtain ⟨Tavg, hTavg, hTavg_bound⟩ := havg
  obtain ⟨Tacc, hTacc, hTacc_bound⟩ := hacc
  have hu1 : oracleComplexity p .averaged ≤ ENNReal.ofReal
      (C * averagingWork (p.n : ℝ) (dimensionlessA p) (dimensionlessB p)) := by
    apply complexity_upper_of_valid_bound (validBudget_of_squaredExpectation hTavg)
    exact hTavg_bound
  have hu2 : oracleComplexity p .averaged ≤ ENNReal.ofReal
      (C * acceleratedWork (p.n : ℝ) (dimensionlessA p) (dimensionlessB p) (complexityLog p)) := by
    apply complexity_upper_of_valid_bound (validBudget_of_threeQuarters hTacc)
    simpa only [acceleratedWork, mul_assoc] using hTacc_bound
  have hi := individualComplexity_le_averaged p
  have hsIS := matching_sandwich_of_complementary_bounds hn hA hB hell hc.le hC.le
    hl1 hl2 (hi.trans hu1) (hi.trans hu2)
  have hsAS := matching_sandwich_of_complementary_bounds hn hA hB hell hc.le hC.le
    (hl1.trans hi) (hl2.trans hi) hu1 hu2
  exact ⟨hsIS.1, hi, hsAS.2⟩

private theorem lowerBudget_of_complexity {p : ProblemParameters}
    {mode : SmoothnessClass} {b : ℝ}
    (h : ENNReal.ofReal b ≤ oracleComplexity p mode) : LowerBudgetBound p mode b := by
  intro budget hbudget
  exact ENNReal.ofReal_le_natCast.mp (h.trans (oracleComplexity_le_of_valid hbudget))

private theorem lowerBudget_either {p : ProblemParameters} {b : ℝ}
    (h : LowerBudgetBound p .individual b) (mode : SmoothnessClass) :
    LowerBudgetBound p mode b := by
  cases mode with
  | individual => exact h
  | averaged => exact lowerBudget_averaged_of_individual h

private theorem upperBudget_either {p : ProblemParameters} {b : ℝ}
    (h : UpperBudgetBound p .averaged b) (mode : SmoothnessClass) :
    UpperBudgetBound p mode b := by
  cases mode with
  | individual => exact upperBudget_individual_of_averaged h
  | averaged => exact h

private theorem averagingWork_le_eight {n A B q : ℝ}
    (hn : 1 ≤ n) (hA : 1 ≤ A) (hB : B ≤ n ^ (1 / 4 : ℝ))
    (hq : 0 ≤ q) (hr : rate n B ≤ 2 * q) :
    averagingWork n A B ≤ 8 * (n + A * q) := by
  have hcoeff := averaging_coefficient_le_twice_rate hn hB
  have hcoeff' : n ^ (1 / 2 : ℝ) * clippedDiameter B + clippedDiameter B ^ 4 ≤ 4 * q := by
    linarith
  have h1 := mul_le_mul_of_nonneg_left hcoeff' (show 0 ≤ 1 + A by linarith)
  have h2 := mul_le_mul_of_nonneg_right (show 1 + A ≤ 2 * A by linarith)
    (show 0 ≤ 4 * q by positivity)
  dsimp [averagingWork]
  nlinarith

private theorem phase_without_log {p : ProblemParameters} {C c q : ℝ} {budget : ℕ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hA : 1 ≤ dimensionlessA p)
    (hB : dimensionlessB p ≤ (p.n : ℝ) ^ (1 / 4 : ℝ)) (hq : 0 ≤ q)
    (hlo : q ≤ rate (p.n : ℝ) (dimensionlessB p))
    (hhi : rate (p.n : ℝ) (dimensionlessB p) ≤ 2 * q)
    (hbudget : ValidBudget p .averaged budget)
    (hbudget_bound : (budget : ℝ) ≤ C *
      averagingWork (p.n : ℝ) (dimensionlessA p) (dimensionlessB p))
    (hlower : LowerBudgetBound p .individual (c * fullRate p))
    (mode : SmoothnessClass) :
    LowerBudgetBound p mode (c * ((p.n : ℝ) + dimensionlessA p * q)) ∧
      UpperBudgetBound p mode ((8 * C) * ((p.n : ℝ) + dimensionlessA p * q)) := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  constructor
  · intro T hT
    apply le_trans _ (lowerBudget_either hlower mode T hT)
    apply mul_le_mul_of_nonneg_left _ hc
    dsimp [fullRate]
    nlinarith only [mul_le_mul_of_nonneg_left hlo (show 0 ≤ dimensionlessA p by linarith)]
  · apply upperBudget_either (mode := mode)
    refine ⟨budget, hbudget, hbudget_bound.trans ?_⟩
    have hw := mul_le_mul_of_nonneg_left (averagingWork_le_eight hn hA hB hq hhi) hC
    nlinarith only [hw]

/-- The sharper phase statement also follows from the two construction
theorems. The small and intermediate upper bounds retain no logarithm. -/
theorem theorem31Piecewise_of_theorem32_and_theorem33
    (hupper : Theorem32Specification) (hlower : Theorem33Specification) :
    Theorem31PiecewiseSpecification := by
  obtain ⟨Astar, c, Cglobal, hAstar, hc, hCglobal, hglobal⟩ :=
    theorem31Global_of_theorem32_and_theorem33 hupper hlower
  obtain ⟨C, hC, hupper⟩ := hupper
  refine ⟨max Astar 1, c, 8 * C, ?_, hc, by positivity, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right Astar 1)
  intro p mode hthreshold
  have hA : 1 ≤ dimensionlessA p := (le_max_right Astar 1).trans hthreshold
  have hglobalp := hglobal p ((le_max_left Astar 1).trans hthreshold)
  have hlowerFull := lowerBudget_of_complexity hglobalp.1
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  have hn0 : (0 : ℝ) ≤ p.n := by positivity
  obtain ⟨havg, hacc⟩ := hupper p
  obtain ⟨Tavg, hTavg, hTavg_bound⟩ := havg
  have hTavg' := validBudget_of_squaredExpectation hTavg
  constructor
  · intro hsmall
    have hquarter : dimensionlessB p ≤ (p.n : ℝ) ^ (1 / 4 : ℝ) :=
      hsmall.trans (Real.rpow_le_rpow_of_exponent_le hn (by norm_num))
    have hr := rate_small_regime hn hsmall
    exact phase_without_log hC.le hc.le hA hquarter (by
      have hb := clippedDiameter_nonneg (dimensionlessB p)
      positivity) hr.1 hr.2 hTavg' hTavg_bound hlowerFull mode
  constructor
  · intro hlo hhi
    have hr := rate_intermediate_regime hn hlo hhi
    exact phase_without_log hC.le hc.le hA hhi (by positivity)
      hr.1 hr.2 hTavg' hTavg_bound hlowerFull mode
  · intro hlarge
    have hr := rate_large_regime hn hlarge
    have he : fullRate p = (p.n : ℝ) + dimensionlessA p *
        ((p.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB p) := by
      dsimp [fullRate]
      rw [hr]
    constructor
    · rw [← he]
      exact lowerBudget_either hlowerFull mode
    · apply upperBudget_either (mode := mode)
      obtain ⟨Tacc, hTacc, hTacc_bound⟩ := hacc
      refine ⟨Tacc, validBudget_of_threeQuarters hTacc, ?_⟩
      have hell := complexityLog_one_le p hA
      have hw := mul_le_mul_of_nonneg_left
        (large_diameter_work_bound hn hA (show 0 ≤ complexityLog p by linarith) hlarge) hC.le
      have hR0 : 0 ≤ fullRate p := by
        dsimp [fullRate]
        exact add_nonneg hn0 (mul_nonneg (dimensionlessA_pos p).le (rate_nonneg hn0))
      have hscale : 0 ≤ C * fullRate p * complexityLog p := by positivity
      rw [← he]
      apply hTacc_bound.trans
      dsimp [acceleratedWork] at hw
      dsimp [fullRate] at hscale ⊢
      nlinarith only [hw, hscale]

end NCConcave16991
