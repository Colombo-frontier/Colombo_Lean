import NCConcave16991.DenseSmoothCalibrationArithmetic
import NCConcave16991.DenseSmoothProblem
import NCConcave16991.DenseWeakRowInformationBudget
import NCConcave16991.ProblemCalibration
import NCConcave16991.BaselineLower

/-! # Public calibration of the sufficient smooth finite-sum lower bound

The concrete normalized probability theorems are the two explicit inputs to
the last assembly. All scaling, rounding and small-n arithmetic are proved.
-/

noncomputable section

namespace NCConcave16991.DenseSmoothCalibration

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open DenseWeakHiding

def gapConstant : ℝ := 2 * DenseSmooth.smoothnessConstant / (1 / 1000 : ℝ) ^ 2
def baselineDenominator : ℝ := 3 + 524288 * gapConstant
def gridBias (n : ℕ) : ℝ := (parityRoundedSqrt n : ℝ) / n

theorem gapConstant_pos : 0 < gapConstant := by
  unfold gapConstant
  exact div_pos (mul_pos (by norm_num) DenseSmooth.smoothnessConstant_pos) (by norm_num)

theorem baselineDenominator_pos : 0 < baselineDenominator := by
  have hK := gapConstant_pos
  unfold baselineDenominator
  positivity

theorem gridBias_pos {n : ℕ} (hn : 0 < n) : 0 < gridBias n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos ((Real.sqrt_pos.mpr hnR).trans_le (parityRoundedSqrt_bounds n).1) hnR

theorem gridBias_sqrt_product {n : ℕ} (hn : 256 ≤ n) :
    1 ≤ Real.sqrt (n : ℝ) * gridBias n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hh := (parityRoundedSqrt_ratio_bounds hn).1
  change (1 : ℝ) / Real.sqrt (n : ℝ) ≤ gridBias n at hh
  simpa only [mul_comm] using (div_le_iff₀ hs).mp hh

theorem grid_row_bias_lower {n : ℕ} (hn : 65536 ≤ n) :
    Real.sqrt (n : ℝ) / 32768 ≤ (rowCost n (gridBias n) : ℝ) * gridBias n := by
  have hρ := gridBias_pos (show 0 < n by omega)
  have hr := mul_le_mul_of_nonneg_right (parityGrid_rowCost_linear hn).1 hρ.le
  change (n : ℝ) / 32768 * gridBias n ≤ (rowCost n (gridBias n) : ℝ) * gridBias n at hr
  have hs := gridBias_sqrt_product (show 256 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnrho : Real.sqrt (n : ℝ) ≤ (n : ℝ) * gridBias n := by
    calc
      Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) * 1 := (mul_one _).symm
      _ ≤ Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) * gridBias n) :=
        mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
      _ = (n : ℝ) * gridBias n := by
        rw [← mul_assoc, ← pow_two, Real.sq_sqrt hn0]
  nlinarith

theorem normalized_A {n T : ℕ} (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) :
    dimensionlessA (DenseSmooth.parameters hn hρ T) = gapConstant * (T + 1 : ℕ) / ρ := by
  unfold dimensionlessA DenseSmooth.parameters gapConstant
  ring

theorem lower_transfer (p : ProblemParameters) {ρ : ℝ} (hρ : 0 < ρ) (T : ℕ)
    (hgap : gapConstant * (T + 1 : ℕ) / ρ ≤ dimensionlessA p)
    {bound : ℝ} (hLower : LowerBudgetBound (DenseSmooth.parameters p.n_pos hρ T) .individual bound) :
    LowerBudgetBound p .individual bound :=
  ProblemCalibration.zeroDiameter_lower_transfer (DenseSmooth.parameters p.n_pos hρ T) p rfl rfl
    (by rwa [normalized_A]) hLower

theorem grid_large_gap_lower (p : ProblemParameters) (hn : 65536 ≤ p.n)
    (hlarge : 4 * gapConstant * Real.sqrt (p.n : ℝ) ≤ dimensionlessA p)
    (hRaw : ∀ T : ℕ, 0 < T →
      LowerBudgetBound (DenseSmooth.parameters p.n_pos (gridBias_pos p.n_pos) T) .individual
        ((rowCost p.n (gridBias p.n) : ℝ) * (T : ℝ) / 2)) :
    LowerBudgetBound p .individual
      (dimensionlessA p * Real.sqrt (p.n : ℝ) / (524288 * gapConstant)) := by
  have hK := gapConstant_pos
  let ρ := gridBias p.n
  have hρ : 0 < ρ := gridBias_pos p.n_pos
  have hs := gridBias_sqrt_product (show 256 ≤ p.n by omega)
  have hm := mul_le_mul_of_nonneg_right hlarge hρ.le
  have hm' := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 4 * gapConstant by positivity)
  have hbound : 4 * gapConstant ≤ dimensionlessA p * ρ := by dsimp [ρ]; nlinarith
  have hb := stageCount_bounds gapConstant_pos hρ hbound
  let J := stageCount (dimensionlessA p) ρ gapConstant - 1
  have hJ : 0 < J := by dsimp [J]; omega
  have he : J + 1 = stageCount (dimensionlessA p) ρ gapConstant := by dsimp [J]; omega
  have hgap : gapConstant * (J + 1 : ℕ) / ρ ≤ dimensionlessA p := by rw [he]; exact hb.2.2.2
  have ht := lower_transfer p hρ J hgap (hRaw J hJ)
  have hc := calibrated_row_cost (dimensionlessA_pos p).le hρ gapConstant_pos
    (Nat.cast_nonneg (rowCost p.n ρ)) hb.2.2.1 (grid_row_bias_lower hn)
  intro budget hbudget
  exact hc.trans (ht budget hbudget)

theorem one_large_gap_lower (p : ProblemParameters) (hn : p.n < 65536)
    (hlarge : 4 * gapConstant * Real.sqrt (p.n : ℝ) ≤ dimensionlessA p)
    (hRaw : ∀ T : ℕ, 0 < T →
      LowerBudgetBound (DenseSmooth.parameters p.n_pos (ρ := 1) (by norm_num) T) .individual (T : ℝ)) :
    LowerBudgetBound p .individual
      (dimensionlessA p * Real.sqrt (p.n : ℝ) / (524288 * gapConstant)) := by
  have hK := gapConstant_pos
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  have hs1 : 1 ≤ Real.sqrt (p.n : ℝ) := by simpa using Real.sqrt_le_sqrt hn1
  have hs2 : Real.sqrt (p.n : ℝ) ≤ 256 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num
      exact hn.le
  have hbound : 4 * gapConstant ≤ dimensionlessA p * 1 := by
    have hh := mul_le_mul_of_nonneg_left hs1 (show (0 : ℝ) ≤ 4 * gapConstant by positivity)
    nlinarith
  have hb := stageCount_bounds gapConstant_pos (show (0 : ℝ) < 1 by norm_num) hbound
  let J := stageCount (dimensionlessA p) 1 gapConstant - 1
  have hJ : 0 < J := by dsimp [J]; omega
  have he : J + 1 = stageCount (dimensionlessA p) 1 gapConstant := by dsimp [J]; omega
  have hgap : gapConstant * (J + 1 : ℕ) / 1 ≤ dimensionlessA p := by rw [he]; exact hb.2.2.2
  have ht := lower_transfer p (ρ := 1) (by norm_num) J hgap (hRaw J hJ)
  have hc := calibrated_row_cost (dimensionlessA_pos p).le (show (0 : ℝ) < 1 by norm_num)
    gapConstant_pos (show (0 : ℝ) ≤ 2 by norm_num) hb.2.2.1
    (show Real.sqrt (p.n : ℝ) / 32768 ≤ (2 : ℝ) * 1 by linarith)
  intro budget hbudget
  have hh := ht budget hbudget
  have hcost : dimensionlessA p * Real.sqrt (p.n : ℝ) / (524288 * gapConstant) ≤ (J : ℝ) := by
    change dimensionlessA p * Real.sqrt (p.n : ℝ) / (524288 * gapConstant) ≤ 2 * (J : ℝ) / 2 at hc
    linarith only [hc]
  exact hcost.trans hh

theorem baseline_lower_from_normalized_sources
    (hGrid : ∀ (n : ℕ) (hn : 65536 ≤ n) (T : ℕ), 0 < T →
      LowerBudgetBound (DenseSmooth.parameters (show 0 < n by omega)
        (gridBias_pos (show 0 < n by omega)) T) .individual
        ((rowCost n (gridBias n) : ℝ) * (T : ℝ) / 2))
    (hOne : ∀ (n : ℕ) (hn : 0 < n) (T : ℕ), 0 < T →
      LowerBudgetBound (DenseSmooth.parameters hn (ρ := 1) (by norm_num) T) .individual (T : ℝ))
    (p : ProblemParameters) (hA : 2 ≤ dimensionlessA p) :
    LowerBudgetBound p .individual
      (((p.n : ℝ) + dimensionlessA p * Real.sqrt (p.n : ℝ)) / baselineDenominator) := by
  have hK := gapConstant_pos
  intro budget hbudget
  have hbase := BaselineProblem.hidden_component_lower p hA budget hbudget
  have hnB : (p.n : ℝ) ≤ 3 * (budget : ℝ) := by linarith
  have hB0 : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  apply (div_le_iff₀ baselineDenominator_pos).mpr
  by_cases hlarge : 4 * gapConstant * Real.sqrt (p.n : ℝ) ≤ dimensionlessA p
  · have hterm : dimensionlessA p * Real.sqrt (p.n : ℝ) / (524288 * gapConstant) ≤ (budget : ℝ) := by
      by_cases hn : 65536 ≤ p.n
      · exact grid_large_gap_lower p hn hlarge (hGrid p.n hn) budget hbudget
      · exact one_large_gap_lower p (lt_of_not_ge hn) hlarge (hOne p.n p.n_pos) budget hbudget
    have hh := (div_le_iff₀ (show (0 : ℝ) < 524288 * gapConstant by positivity)).mp hterm
    unfold baselineDenominator
    nlinarith only [hnB, hh]
  · have hh := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hlarge)) (Real.sqrt_nonneg (p.n : ℝ))
    have he : (4 * gapConstant * Real.sqrt (p.n : ℝ)) * Real.sqrt (p.n : ℝ) =
        4 * gapConstant * (p.n : ℝ) := by
      rw [mul_assoc, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg p.n)]
    rw [he] at hh
    have hm := mul_le_mul_of_nonneg_left hnB (show (0 : ℝ) ≤ 1 + 4 * gapConstant by positivity)
    have hcoef : 3 * (1 + 4 * gapConstant) ≤ baselineDenominator := by
      unfold baselineDenominator
      linarith [gapConstant_pos]
    have hlast := mul_le_mul_of_nonneg_right hcoef hB0
    nlinarith only [hh, hm, hlast]

end NCConcave16991.DenseSmoothCalibration
