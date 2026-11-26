import NCConcave16991.ProblemCalibration

/-! # Exact same-budget public calibration with nonzero dual diameter -/

noncomputable section

namespace NCConcave16991.ProblemCalibration

set_option backward.isDefEq.respectTransparency false

theorem scaled_diameter_le (source target : ProblemParameters)
    (hB : dimensionlessB source ≤ dimensionlessB target) :
    source.diameter / spaceScale source target ≤ target.diameter := by
  apply (div_le_iff₀ (spaceScale_pos source target)).mpr
  have hh := (div_le_div_iff₀ source.epsilon_pos target.epsilon_pos).mp hB
  calc
    source.diameter ≤ (target.L * target.diameter * source.epsilon) /
        (target.epsilon * source.L) :=
      (le_div_iff₀ (mul_pos target.epsilon_pos source.L_pos)).mpr (by nlinarith only [hh])
    _ = target.diameter * spaceScale source target := by unfold spaceScale; ring

private theorem parameter_ext (p q : ProblemParameters) (hn : p.n = q.n) (hL : p.L = q.L)
    (hgap : p.gap = q.gap) (heps : p.epsilon = q.epsilon) (hD : p.diameter = q.diameter) : p = q := by
  cases p
  cases q
  simp_all

theorem diameter_lower_transfer (source target : ProblemParameters)
    (hn : source.n = target.n) (hA : dimensionlessA source ≤ dimensionlessA target)
    (hB : dimensionlessB source ≤ dimensionlessB target)
    {bound : ℝ} (hLower : LowerBudgetBound source .individual bound) :
    LowerBudgetBound target .individual bound := by
  let a := valueScale source target
  let b := spaceScale source target
  have ha : 0 < a := valueScale_pos source target
  have hb : 0 < b := spaceScale_pos source target
  let scaled := ProblemScaling.parameters source a b ha hb
  have hgap : scaled.gap ≤ target.gap := scaled_gap_le source target hA
  have hdiam : scaled.diameter ≤ target.diameter := scaled_diameter_le source target hB
  have heps : target.epsilon ≤ scaled.epsilon := by
    change target.epsilon ≤ a * b * source.epsilon
    rw [show a * b * source.epsilon = target.epsilon from scaled_epsilon source target]
  have hs := ProblemScaling.lowerBudget_transfer source ha hb hLower
  have ht := ProblemBounds.lowerBudget_transfer scaled target.gap_pos target.epsilon_pos
    target.diameter_nonneg hgap hdiam heps hs
  have heq : ProblemBounds.parameters scaled target.gap target.epsilon target.diameter
      target.gap_pos target.epsilon_pos target.diameter_nonneg = target := by
    apply parameter_ext
    · exact hn
    · exact scaled_L source target
    · rfl
    · rfl
    · rfl
  rw [heq] at ht
  exact ht

end NCConcave16991.ProblemCalibration
