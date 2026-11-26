import NCConcave16991.ProblemScalingPolicy
import NCConcave16991.ProblemBounds

/-! # Exact public-parameter calibration of zero-dual-diameter lower bounds -/

noncomputable section

namespace NCConcave16991.ProblemCalibration

set_option backward.isDefEq.respectTransparency false

def valueScale (source target : ProblemParameters) : ℝ :=
  target.epsilon ^ 2 * source.L / (target.L * source.epsilon ^ 2)

def spaceScale (source target : ProblemParameters) : ℝ :=
  target.L * source.epsilon / (target.epsilon * source.L)

theorem valueScale_pos (source target : ProblemParameters) : 0 < valueScale source target :=
  div_pos (mul_pos (sq_pos_of_pos target.epsilon_pos) source.L_pos)
    (mul_pos target.L_pos (sq_pos_of_pos source.epsilon_pos))

theorem spaceScale_pos (source target : ProblemParameters) : 0 < spaceScale source target :=
  div_pos (mul_pos target.L_pos source.epsilon_pos) (mul_pos target.epsilon_pos source.L_pos)

theorem scaled_L (source target : ProblemParameters) :
    valueScale source target * spaceScale source target ^ 2 * source.L = target.L := by
  unfold valueScale spaceScale
  field_simp [source.L_pos.ne', target.L_pos.ne', source.epsilon_pos.ne', target.epsilon_pos.ne']
  <;> ring

theorem scaled_epsilon (source target : ProblemParameters) :
    valueScale source target * spaceScale source target * source.epsilon = target.epsilon := by
  unfold valueScale spaceScale
  field_simp [source.L_pos.ne', target.L_pos.ne', source.epsilon_pos.ne', target.epsilon_pos.ne']
  <;> ring

theorem scaled_gap_le (source target : ProblemParameters)
    (hA : dimensionlessA source ≤ dimensionlessA target) :
    valueScale source target * source.gap ≤ target.gap := by
  have hh := (div_le_div_iff₀ (sq_pos_of_pos source.epsilon_pos)
    (sq_pos_of_pos target.epsilon_pos)).mp hA
  unfold valueScale
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos target.L_pos (sq_pos_of_pos source.epsilon_pos))).mpr
  nlinarith only [hh]

private theorem parameters_ext (p q : ProblemParameters) (hn : p.n = q.n) (hL : p.L = q.L)
    (hgap : p.gap = q.gap) (heps : p.epsilon = q.epsilon) (hD : p.diameter = q.diameter) : p = q := by
  cases p
  cases q
  simp_all

/-- This transfers the actual uniformly valid randomized-policy lower bound
with the identical fixed query budget and private seed law. -/
theorem zeroDiameter_lower_transfer (source target : ProblemParameters)
    (hn : source.n = target.n) (hzero : source.diameter = 0)
    (hA : dimensionlessA source ≤ dimensionlessA target)
    {bound : ℝ} (hLower : LowerBudgetBound source .individual bound) :
    LowerBudgetBound target .individual bound := by
  let a := valueScale source target
  let b := spaceScale source target
  have ha : 0 < a := valueScale_pos source target
  have hb : 0 < b := spaceScale_pos source target
  let scaled := ProblemScaling.parameters source a b ha hb
  have hgap : scaled.gap ≤ target.gap := scaled_gap_le source target hA
  have hdiam : scaled.diameter ≤ target.diameter := by
    change source.diameter / b ≤ target.diameter
    rw [hzero, zero_div]
    exact target.diameter_nonneg
  have heps : target.epsilon ≤ scaled.epsilon := by
    change target.epsilon ≤ a * b * source.epsilon
    rw [show a * b * source.epsilon = target.epsilon from scaled_epsilon source target]
  have hs := ProblemScaling.lowerBudget_transfer source ha hb hLower
  have ht := ProblemBounds.lowerBudget_transfer scaled target.gap_pos target.epsilon_pos
    target.diameter_nonneg hgap hdiam heps hs
  have heq : ProblemBounds.parameters scaled target.gap target.epsilon target.diameter
      target.gap_pos target.epsilon_pos target.diameter_nonneg = target := by
    apply parameters_ext
    · exact hn
    · exact scaled_L source target
    · rfl
    · rfl
    · rfl
  rw [heq] at ht
  exact ht

end NCConcave16991.ProblemCalibration
