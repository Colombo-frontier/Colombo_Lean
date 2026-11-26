import MatchingBounds1005.AnalyticFamily

/-! The last readout remains hidden for a horizon proportional to ε^(-5/3),
using the actual integer layer index rather than just the path dimension. -/
noncomputable section

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration PathGreen

def calendarHorizon (p : ℕ) (t : ℝ) : ℕ :=
  phaseCount (amplitudeConstant p) t *
    ((pathEdges (pathScale (amplitudeConstant p) (scale p) t) + 2) / 2)

theorem calendarHorizon_integer_bounds (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ parameterThreshold p) :
    phaseCount (amplitudeConstant p) t * pathSize (pathScale (amplitudeConstant p) (scale p) t) ≤
      2 * calendarHorizon p t ∧
    calendarHorizon p t ≤ phaseCount (amplitudeConstant p) t *
      pathSize (pathScale (amplitudeConstant p) (scale p) t) := by
  have hm := (ceiling_scale _
    (pathScale_pos _ _ _ (amplitudeConstant_pos p) (scale_pos p) ht) (path_small p ht hsmall)).1
  have hlo : pathSize (pathScale (amplitudeConstant p) (scale p) t) ≤
      2 * ((pathEdges (pathScale (amplitudeConstant p) (scale p) t) + 2) / 2) := by omega
  have hup : ((pathEdges (pathScale (amplitudeConstant p) (scale p) t) + 2) / 2) ≤
      pathSize (pathScale (amplitudeConstant p) (scale p) t) := by omega
  constructor
  · exact (Nat.mul_le_mul_left _ hlo).trans_eq (by unfold calendarHorizon; ring)
  · exact Nat.mul_le_mul_left _ hup

theorem calendarHorizon_bounds (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ parameterThreshold p) :
    (horizonLower p / 2) * Model.rate (t ^ 3) ≤ (calendarHorizon p t : ℝ) ∧
      (calendarHorizon p t : ℝ) ≤ horizonUpper p * Model.rate (t ^ 3) := by
  obtain ⟨hlo, hup⟩ := calendarHorizon_integer_bounds p t ht hsmall
  obtain ⟨hl, hu⟩ := horizon_bounds p t ht hsmall
  have hlo' : ((phaseCount (amplitudeConstant p) t *
      pathSize (pathScale (amplitudeConstant p) (scale p) t) : ℕ) : ℝ) ≤
        2 * (calendarHorizon p t : ℝ) := by exact_mod_cast hlo
  have hup' : (calendarHorizon p t : ℝ) ≤ ((phaseCount (amplitudeConstant p) t *
      pathSize (pathScale (amplitudeConstant p) (scale p) t) : ℕ) : ℝ) := by exact_mod_cast hup
  constructor
  · nlinarith only [hl, hlo']
  · exact hup'.trans hu

theorem query_before_last_layer (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ parameterThreshold p) (T : ℕ)
    (hT : (T : ℝ) < (horizonLower p / 2) * Model.rate (t ^ 3)) :
    T < calendarHorizon p t := by
  exact_mod_cast hT.trans_le (calendarHorizon_bounds p t ht hsmall).1

theorem accuracy_calendarHorizon_bounds (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold p) :
    (horizonLower p / 2) * Model.rate ε ≤ (calendarHorizon p (accuracyParameter ε) : ℝ) ∧
      (calendarHorizon p (accuracyParameter ε) : ℝ) ≤ horizonUpper p * Model.rate ε := by
  simpa only [accuracyParameter_cube hε.le] using calendarHorizon_bounds p (accuracyParameter ε)
    (accuracy_parameters p hε hsmall).1 (accuracy_parameters p hε hsmall).2.1

end MatchingBounds1005.AnalyticFamily
