import MatchingBounds1005.ActualInformationBudget
import MatchingBounds1005.CandidateCalendar

/-! Explicit positive final thresholds, query constant, and dimension
constant. The proved source budget and reference failure probability make
both the rare-event entropy transfer and the Pinsker bound at most 1/15. -/
noncomputable section

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration

def lowerThreshold (p : ℕ) : ℝ :=
  min (geometryThreshold p) (min (candidateThreshold p) (1 / (10000 * (informationConstant p + 1))))

theorem lowerThreshold_pos (p : ℕ) : 0 < lowerThreshold p := by
  have hg := geometryThreshold_pos p
  have hc := candidateThreshold_pos p
  have hi := informationConstant_pos p
  unfold lowerThreshold
  positivity

theorem lowerThreshold_le_geometry (p : ℕ) : lowerThreshold p ≤ geometryThreshold p := min_le_left _ _

theorem lowerThreshold_le_candidate (p : ℕ) : lowerThreshold p ≤ candidateThreshold p :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem lowerThreshold_le_parameter (p : ℕ) : lowerThreshold p ≤ parameterThreshold p :=
  (lowerThreshold_le_geometry p).trans (geometryThreshold_le_parameter p)

theorem final_small_bounds (p : ℕ) {t : ℝ} (ht : 0 < t) (hsmall : t ≤ lowerThreshold p) :
    t ≤ 1 / 10000 ∧ informationConstant p * t ≤ 1 / 10000 := by
  have hC := informationConstant_pos p
  have hs : t ≤ 1 / (10000 * (informationConstant p + 1)) :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hm := (le_div_iff₀ (by positivity : 0 < 10000 * (informationConstant p + 1))).mp hs
  have hprod := mul_nonneg hC.le ht.le
  constructor <;> nlinarith only [hm, hprod, ht]

theorem final_budget_bound (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ lowerThreshold p) :
    sourceInformationBudget p t ht (hsmall.trans (lowerThreshold_le_parameter p)) ≤ 1 / 10000 := by
  have hb := sourceInformationBudget_bound p t ht (hsmall.trans (lowerThreshold_le_geometry p))
  obtain ⟨htsmall, hCt⟩ := final_small_bounds p ht hsmall
  have ht1 : t ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.le ht1
  have ht3 : t ^ 3 ≤ t := by nlinarith only [mul_le_mul_of_nonneg_left ht2 ht.le]
  exact hb.trans ((mul_le_mul_of_nonneg_left ht3 (informationConstant_pos p).le).trans hCt)

theorem final_bad_mass_bound (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ lowerThreshold p) :
    1 / (powerCopies t : ℝ) ^ 4 ≤ 1 / 10000 := by
  have hb := PowerInformation.inverse_fourth_bound ht (powerCopies_lower (t := t))
  have htsmall := (final_small_bounds p ht hsmall).1
  have ht1 : t ≤ 1 := by linarith
  have ht168 : t ^ 168 ≤ t := by
    simpa only [pow_one] using pow_le_pow_of_le_one ht.le ht1 (by omega : 1 ≤ 168)
  exact hb.trans (ht168.trans htsmall)

theorem final_transfer_bound (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ lowerThreshold p) :
    1 / (powerCopies t : ℝ) ^ 4 +
      Real.sqrt (2 * sourceInformationBudget p t ht (hsmall.trans (lowerThreshold_le_parameter p))) ≤ 1 / 15 := by
  have hbad := final_bad_mass_bound p t ht hsmall
  have hbudget := final_budget_bound p t ht hsmall
  have hsqrt : Real.sqrt (2 * sourceInformationBudget p t ht
      (hsmall.trans (lowerThreshold_le_parameter p))) ≤ 1 / 50 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by linarith only [hbudget]⟩
  linarith only [hbad, hsqrt]

/-- The sharper rare-event entropy transfer used by EventTransfer. -/
theorem final_entropy_transfer_bound (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ lowerThreshold p) :
    (4 / 3 : ℝ) *
      (sourceInformationBudget p t ht (hsmall.trans (lowerThreshold_le_parameter p)) +
        Real.log 4 * (1 / (powerCopies t : ℝ) ^ 4)) ≤ 1 / 15 := by
  have hbad := final_bad_mass_bound p t ht hsmall
  have hbudget := final_budget_bound p t ht hsmall
  have hlog : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith only [h]
  have hm := mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ 1 / (powerCopies t : ℝ) ^ 4 by positivity)
  linarith only [hbad, hbudget, hm]

def lowerConstant (p : ℕ) : ℝ := horizonLower p / 8
def dimensionConstant (p : ℕ) : ℝ := 3 * horizonUpper p
def lowerAccuracyThreshold (p : ℕ) : ℝ := lowerThreshold p ^ 3

theorem lowerConstant_pos (p : ℕ) : 0 < lowerConstant p := div_pos (horizonLower_pos p) (by norm_num)
theorem dimensionConstant_pos (p : ℕ) : 0 < dimensionConstant p := mul_pos (by norm_num) (horizonUpper_pos p)
theorem lowerAccuracyThreshold_pos (p : ℕ) : 0 < lowerAccuracyThreshold p := pow_pos (lowerThreshold_pos p) 3

theorem final_accuracy_parameters (p : ℕ) {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ lowerAccuracyThreshold p) :
    0 < accuracyParameter ε ∧ accuracyParameter ε ≤ lowerThreshold p ∧ accuracyParameter ε ^ 3 = ε :=
  ⟨accuracyParameter_pos hε, accuracyParameter_small hε.le (lowerThreshold_pos p).le hsmall,
    accuracyParameter_cube hε.le⟩

theorem final_query_budget (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    candidateBudget p (accuracyParameter ε) = Nat.floor (lowerConstant p * Model.rate ε) := by
  unfold candidateBudget lowerConstant
  rw [accuracyParameter_cube hε.le]

theorem final_candidate_safe (p : ℕ) {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ lowerAccuracyThreshold p) :
    Nat.floor (lowerConstant p * Model.rate ε) + 1 < calendarHorizon p (accuracyParameter ε) := by
  rw [← final_query_budget p hε]
  exact candidateBudget_safe p _ (final_accuracy_parameters p hε hsmall).1
    ((final_accuracy_parameters p hε hsmall).2.1.trans (lowerThreshold_le_candidate p))

theorem final_dimension_bound (p : ℕ) {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ lowerAccuracyThreshold p) :
    (dimension p (accuracyParameter ε) (powerCopies (accuracyParameter ε)) : ℝ) ≤
      dimensionConstant p * ε ^ (-(47 : ℝ) / 3) := by
  obtain ⟨ht, htδ, he⟩ := final_accuracy_parameters p hε hsmall
  have h := power_dimension_upper p (accuracyParameter ε) ht (htδ.trans (lowerThreshold_le_parameter p))
  have hr := cube_dimension_rate ht
  rw [he] at hr
  rw [hr, mul_one_div]
  exact h

end MatchingBounds1005.AnalyticFamily
