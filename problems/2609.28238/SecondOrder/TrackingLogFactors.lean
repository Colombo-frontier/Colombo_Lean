import SecondOrder.OptimizedRequestBudget
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace SecondOrder
noncomputable section

theorem trackingTreeDepth_eq_log (M : ℕ) :
    trackingTreeDepth M = 1+⌈Real.logb 2 (M+1 : ℕ)⌉₊ := by
  rw [trackingTreeDepth,← Real.natCeil_logb_natCast 2 (M+1)]
  norm_num

theorem trackingTreeDepth_log_bound (M : ℕ) :
    (trackingTreeDepth M : ℝ) < 2+Real.logb 2 ((M : ℝ)+1) := by
  have hn : 0 ≤ Real.logb 2 ((M : ℝ)+1) :=
    Real.logb_nonneg (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg M))
  have hc := Nat.ceil_lt_add_one hn
  rw [trackingTreeDepth_eq_log]
  push_cast
  linarith

theorem localFailureTolerance_inverse (M : ℕ) : 1/localFailureTolerance M = 384*((M : ℝ)+1) := by
  unfold localFailureTolerance
  push_cast
  simp only [one_div_one_div]
  ring

theorem localConfidenceFactor_eq (M : ℕ) :
    8*Real.log (1/localFailureTolerance M)+2 = 8*Real.log 384+8*Real.log ((M : ℝ)+1)+2 := by
  rw [localFailureTolerance_inverse,Real.log_mul (by norm_num) (by positivity)]
  ring

theorem physicalCap_upper (P : Parameters) (ν τ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    (physicalCap P ν τ γ : ℝ) < 25+24*idealMoveBudget P ν τ γ := by
  have hB := idealMoveBudget_nonneg P ν τ γ hγ
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 24*(1+idealMoveBudget P ν τ γ) by positivity)
  change (physicalCap P ν τ γ : ℝ) < _ at hc
  linarith

def depthLogEnvelope (P : Parameters) (ν τ γ : ℝ) : ℝ :=
  2+Real.logb 2 (26+24*idealMoveBudget P ν τ γ)

def confidenceLogEnvelope (P : Parameters) (ν τ γ : ℝ) : ℝ :=
  8*Real.log 384+8*Real.log (26+24*idealMoveBudget P ν τ γ)+2

theorem selectedDepth_log_bound (P : Parameters) (ν τ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    (trackingTreeDepth (physicalCap P ν τ γ) : ℝ) ≤ depthLogEnvelope P ν τ γ := by
  apply (trackingTreeDepth_log_bound _).le.trans
  apply add_le_add_left
  exact Real.logb_le_logb_of_le (by norm_num) (by positivity)
    (by have hc := physicalCap_upper P ν τ hγ; linarith)

theorem depthLogEnvelope_pos (P : Parameters) (ν τ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    0 < depthLogEnvelope P ν τ γ :=
  lt_of_lt_of_le (Nat.cast_pos.mpr (trackingTreeDepth_pos _)) (selectedDepth_log_bound P ν τ hγ)

theorem selectedConfidence_log_bound (P : Parameters) (ν τ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    8*Real.log (1/localFailureTolerance (physicalCap P ν τ γ))+2 ≤ confidenceLogEnvelope P ν τ γ := by
  rw [localConfidenceFactor_eq]
  have hl := Real.log_le_log (show (0 : ℝ) < (physicalCap P ν τ γ : ℝ)+1 by positivity)
    (show (physicalCap P ν τ γ : ℝ)+1 ≤ 26+24*idealMoveBudget P ν τ γ by
      have hc := physicalCap_upper P ν τ hγ
      linarith)
  unfold confidenceLogEnvelope
  linarith

theorem confidenceLogEnvelope_nonneg (P : Parameters) (ν τ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    0 ≤ confidenceLogEnvelope P ν τ γ :=
  (chordConfidenceFactor_nonneg (localFailureTolerance_pos _) (localFailureTolerance_le_one _)).trans
    (selectedConfidence_log_bound P ν τ hγ)

theorem selected_log_factors_bound (P : Parameters) (ν τ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    (trackingTreeDepth (physicalCap P ν τ γ) : ℝ)^3*
      (8*Real.log (1/localFailureTolerance (physicalCap P ν τ γ))+2) ≤
        (depthLogEnvelope P ν τ γ)^3*confidenceLogEnvelope P ν τ γ :=
  mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (selectedDepth_log_bound P ν τ hγ) 3)
    (selectedConfidence_log_bound P ν τ hγ)
    (chordConfidenceFactor_nonneg (localFailureTolerance_pos _) (localFailureTolerance_le_one _))
    (pow_nonneg (depthLogEnvelope_pos P ν τ hγ).le _)

/-- All rounding and finite-cap overheads are bounded explicitly. The
depth and confidence factors are real logarithms of the move budget. -/
theorem selectedQueryCap_log_bound (P : Parameters) (ν : ℝ) {τ γ : ℝ}
    (hτ : 0 < τ) (hγ : 0 < γ) (κ : ℕ) :
    (selectedQueryCap P ν τ γ κ : ℝ) <
      25+24*(6144*(depthLogEnvelope P ν τ γ)^3*confidenceLogEnvelope P ν τ γ*
        optimizedTrackingScale P ν τ γ+
        (1+16*P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2))*(κ : ℝ)) := by
  apply (selectedQueryCap_bound P ν hτ hγ κ).trans_le
  have hp := mul_le_mul_of_nonneg_right (selected_log_factors_bound P ν τ hγ)
    (optimizedTrackingScale_pos P ν hτ hγ).le
  nlinarith

end
end SecondOrder
