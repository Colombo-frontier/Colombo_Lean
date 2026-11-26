import MatchingBounds1005.AnalyticFirstExitBound

/-! The exact manuscript lower-bound target, with one policy-independent
fixed instance distribution and the stated dimension and accuracy exponents. -/
noncomputable section
namespace MatchingBounds1005.Model
open AnalyticFamily EpsilonCalibration

theorem main_lower_bound : MainLowerBound := by
  intro p hp
  refine ⟨lowerConstant p, dimensionConstant p, lowerAccuracyThreshold p,
    lowerConstant_pos p, dimensionConstant_pos p, lowerAccuracyThreshold_pos p, ?_⟩
  intro ε hε hsmall
  obtain ⟨ht, hs, he⟩ := final_accuracy_parameters p hε hsmall
  refine ⟨dimension p (accuracyParameter ε) (powerCopies (accuracyParameter ε)),
    dimension_pos p (accuracyParameter ε) ht (hs.trans (lowerThreshold_le_parameter p)) _, ?_, ?_⟩
  · simpa only [dimensionRate, neg_div] using final_dimension_bound p hε hsmall
  · have h := actual_hardDistribution p (by omega) (accuracyParameter ε) ht hs
    rw [final_query_budget p hε, he] at h
    exact h

end MatchingBounds1005.Model
