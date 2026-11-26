import NCConcave16991.ConeCalibrationScaling
import NCConcave16991.BaselineLower

/-! # Regime assembly of the cone calibration

This is a transparent reduction: the normalized cone lower theorem is supplied
by the concrete Haar coupling and the smooth finite-sum lower theorem by the
independent smooth construction. Neither is asserted as an axiom here.
-/

noncomputable section

namespace NCConcave16991.ConeCalibration

def coneDenominator : ℝ := 400 * 4096 * gapScale * diameterThreshold
def regimeDenominator : ℝ := 6 + 2 * coneDenominator

theorem coneDenominator_pos : 0 < coneDenominator := by
  exact mul_pos (mul_pos (by norm_num) gapScale_pos) diameterThreshold_pos

theorem regimeDenominator_pos : 0 < regimeDenominator := by
  have hh := coneDenominator_pos
  unfold regimeDenominator
  positivity

theorem cone_regime_lower (p : ProblemParameters) (hn : 65536 ≤ (p.n : ℝ))
    (hB : diameterThreshold ≤ dimensionlessB p) (hA : 2 ≤ dimensionlessA p)
    (hLower : LowerBudgetBound (normalizedParameters p hn hB) .individual
      ((p.n : ℝ) * (publicStageIndex p + 1 : ℕ) / 4096)) :
    LowerBudgetBound p .individual
      (((p.n : ℝ) + dimensionlessA p * optimizationLower (p.n : ℝ) (dimensionlessB p)) / regimeDenominator) := by
  intro T hT
  have hb := BaselineProblem.hidden_component_lower p hA T hT
  have hnT : (p.n : ℝ) ≤ 3 * (T : ℝ) := by nlinarith
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  apply (div_le_iff₀ regimeDenominator_pos).mpr
  by_cases hlarge : 400 * gapScale * publicRatio p ≤ dimensionlessA p
  · have hc := lowerBudget_of_normalized p hn hB hlarge hLower T hT
    change dimensionlessA p * optimizationLower (p.n : ℝ) (dimensionlessB p) / coneDenominator ≤ (T : ℝ) at hc
    have hc' := (div_le_iff₀ coneDenominator_pos).mp hc
    have hden : 3 + coneDenominator ≤ regimeDenominator := by
      unfold regimeDenominator
      linarith [coneDenominator_pos]
    have hm := mul_le_mul_of_nonneg_right hden hT0
    nlinarith
  · have hc := small_gap_covered hn diameterThreshold_ge_one hB gapScale_pos
      (dimensionlessA_pos p).le (lt_of_not_ge hlarge)
    have hKBC : 0 < gapScale * diameterThreshold := mul_pos gapScale_pos diameterThreshold_pos
    have hcoef : 3 * (1 + 400 * gapScale * diameterThreshold) ≤ regimeDenominator := by
      unfold regimeDenominator coneDenominator
      nlinarith
    have hnMul := mul_le_mul_of_nonneg_left hnT (by nlinarith [hKBC] : 0 ≤ 1 + 400 * gapScale * diameterThreshold)
    have hbound := mul_le_mul_of_nonneg_right hcoef hT0
    nlinarith

def globalDenominator (smoothDenominator : ℝ) : ℝ :=
  regimeDenominator + (diameterThreshold + 16) * smoothDenominator + 1

theorem globalDenominator_pos {S : ℝ} (hS : 0 < S) : 0 < globalDenominator S := by
  have hr := regimeDenominator_pos
  have hd := diameterThreshold_pos
  unfold globalDenominator
  positivity

/-- A precise final arithmetic interface for the optimization-type term.
Both lower-bound inputs remain explicit until their concrete information
proofs are instantiated by the caller. -/
theorem optimization_lower_from_sources (p : ProblemParameters) (hA : 2 ≤ dimensionlessA p)
    {S : ℝ} (hS : 0 < S)
    (hSmooth : LowerBudgetBound p .individual
      (((p.n : ℝ) + dimensionlessA p * Real.sqrt (p.n : ℝ)) / S))
    (hCone : ∀ (hn : 65536 ≤ (p.n : ℝ)) (hB : diameterThreshold ≤ dimensionlessB p),
      LowerBudgetBound (normalizedParameters p hn hB) .individual
        ((p.n : ℝ) * (publicStageIndex p + 1 : ℕ) / 4096)) :
    LowerBudgetBound p .individual
      (((p.n : ℝ) + dimensionlessA p * optimizationLower (p.n : ℝ) (dimensionlessB p)) / globalDenominator S) := by
  have hden := globalDenominator_pos hS
  intro T hT
  apply (div_le_iff₀ hden).mpr
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  by_cases hn : 65536 ≤ (p.n : ℝ)
  · by_cases hB : diameterThreshold ≤ dimensionlessB p
    · have hc := cone_regime_lower p hn hB hA (hCone hn hB) T hT
      have hc' := (div_le_iff₀ regimeDenominator_pos).mp hc
      have hden' : regimeDenominator ≤ globalDenominator S := by
        unfold globalDenominator
        have hh := mul_pos (by linarith [diameterThreshold_pos] : 0 < diameterThreshold + 16) hS
        linarith
      exact hc'.trans (mul_le_mul_of_nonneg_left hden' hT0)
    · have hopt := optimization_small_diameter (show 0 ≤ (p.n : ℝ) by positivity)
        diameterThreshold_ge_one (le_of_lt (lt_of_not_ge hB))
      have hweak : optimizationLower (p.n : ℝ) (dimensionlessB p) ≤
          (diameterThreshold + 16) * Real.sqrt (p.n : ℝ) := by
        nlinarith [Real.sqrt_nonneg (p.n : ℝ)]
      have hs := (div_le_iff₀ hS).mp (hSmooth T hT)
      have hnum := mul_le_mul_of_nonneg_left hweak (dimensionlessA_pos p).le
      have hn0 : (0 : ℝ) ≤ p.n := by positivity
      have hfactor : 0 < diameterThreshold + 16 := by linarith [diameterThreshold_pos]
      have hm := mul_le_mul_of_nonneg_left hs hfactor.le
      have hD : (diameterThreshold + 16) * S ≤ globalDenominator S := by
        unfold globalDenominator
        linarith [regimeDenominator_pos]
      have hDT := mul_le_mul_of_nonneg_right hD hT0
      nlinarith [mul_nonneg (by linarith [diameterThreshold_ge_one] : 0 ≤ diameterThreshold + 15) hn0]
  · have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
    have hopt := optimization_small_n (B := dimensionlessB p) hn1 (le_of_lt (lt_of_not_ge hn))
    have hweak : optimizationLower (p.n : ℝ) (dimensionlessB p) ≤
        (diameterThreshold + 16) * Real.sqrt (p.n : ℝ) := by
      nlinarith [mul_nonneg diameterThreshold_pos.le (Real.sqrt_nonneg (p.n : ℝ))]
    have hs := (div_le_iff₀ hS).mp (hSmooth T hT)
    have hnum := mul_le_mul_of_nonneg_left hweak (dimensionlessA_pos p).le
    have hn0 : (0 : ℝ) ≤ p.n := by positivity
    have hfactor : 0 < diameterThreshold + 16 := by linarith [diameterThreshold_pos]
    have hm := mul_le_mul_of_nonneg_left hs hfactor.le
    have hD : (diameterThreshold + 16) * S ≤ globalDenominator S := by
      unfold globalDenominator
      linarith [regimeDenominator_pos]
    have hDT := mul_le_mul_of_nonneg_right hD hT0
    nlinarith [mul_nonneg (by linarith [diameterThreshold_ge_one] : 0 ≤ diameterThreshold + 15) hn0]

end NCConcave16991.ConeCalibration
