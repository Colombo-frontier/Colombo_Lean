import NCConcave16991.ConeAdmissibility
import NCConcave16991.ConeCalibrationAlgebra
import NCConcave16991.ProblemScalingPolicy
import NCConcave16991.ProblemBounds

/-! # Actual public-parameter scaling of the normalized cone construction

The arithmetic and policy transfer are independent of the remaining Haar
coupling theorem. The final reduction takes a proved normalized lower bound
as its input and preserves its literal query budget.
-/

noncomputable section

namespace NCConcave16991.ConeCalibration

open ConeSmooth

set_option backward.isDefEq.respectTransparency false

def delta : ℝ := 1 / 1000
def diameterThreshold : ℝ := 2 * individualConstant / delta
def gapScale : ℝ := individualConstant / delta ^ 2

theorem delta_pos : 0 < delta := by norm_num [delta]
theorem diameterThreshold_pos : 0 < diameterThreshold :=
  div_pos (mul_pos (by norm_num) individualConstant_pos) delta_pos
theorem gapScale_pos : 0 < gapScale := div_pos individualConstant_pos (sq_pos_of_pos delta_pos)
theorem diameterThreshold_ge_one : 1 ≤ diameterThreshold := by
  have hc := densitySlopeBound_nonneg
  norm_num [diameterThreshold, delta, individualConstant]
  nlinarith

def publicRadius (p : ProblemParameters) : ℝ := radius (p.n : ℝ) (dimensionlessB p) diameterThreshold
def publicRatio (p : ProblemParameters) : ℝ := clockRatio (p.n : ℝ) (dimensionlessB p) diameterThreshold
def publicStageCount (p : ProblemParameters) : ℕ := stageCount (dimensionlessA p) gapScale (publicRatio p)
def publicStageIndex (p : ProblemParameters) : ℕ := stageIndex (dimensionlessA p) gapScale (publicRatio p)

theorem publicRadius_bounds (p : ProblemParameters) (hn : 65536 ≤ (p.n : ℝ))
    (hB : diameterThreshold ≤ dimensionlessB p) :
    1 ≤ publicRadius p ∧ publicRadius p ≤ dimensionlessB p / diameterThreshold ∧
      publicRadius p ≤ quarterRoot (p.n : ℝ) := radius_bounds hn diameterThreshold_ge_one hB

theorem publicRatio_bounds (p : ProblemParameters) (hn : 65536 ≤ (p.n : ℝ))
    (hB : diameterThreshold ≤ dimensionlessB p) :
    16 ≤ publicRatio p ∧ Real.sqrt (p.n : ℝ) ≤ publicRatio p ^ 2 ∧
      Real.sqrt (p.n : ℝ) = publicRatio p * publicRadius p := clockRatio_bounds hn diameterThreshold_ge_one hB

def normalizedParameters (p : ProblemParameters) (hn : 65536 ≤ (p.n : ℝ))
    (hB : diameterThreshold ≤ dimensionlessB p) : ProblemParameters :=
  ConeProblem.parameters p.n p.n_pos (publicStageIndex p) individualConstant individualConstant_pos
    (publicRadius p) (by have hh := (publicRadius_bounds p hn hB).1; linarith)
    (publicRatio p) (by have hh := (publicRatio_bounds p hn hB).1; linarith)

def valueScale (p : ProblemParameters) : ℝ :=
  p.epsilon ^ 2 * individualConstant / (p.L * delta ^ 2)
def spaceScale (p : ProblemParameters) : ℝ := p.L * delta / (p.epsilon * individualConstant)

theorem valueScale_pos (p : ProblemParameters) : 0 < valueScale p :=
  div_pos (mul_pos (sq_pos_of_pos p.epsilon_pos) individualConstant_pos)
    (mul_pos p.L_pos (sq_pos_of_pos delta_pos))
theorem spaceScale_pos (p : ProblemParameters) : 0 < spaceScale p :=
  div_pos (mul_pos p.L_pos delta_pos) (mul_pos p.epsilon_pos individualConstant_pos)

theorem valueScale_eq (p : ProblemParameters) : valueScale p = p.epsilon ^ 2 * gapScale / p.L := by
  unfold valueScale gapScale
  ring

theorem scaled_L (p : ProblemParameters) : valueScale p * spaceScale p ^ 2 * individualConstant = p.L := by
  unfold valueScale spaceScale
  field_simp [p.L_pos.ne', p.epsilon_pos.ne', individualConstant_pos.ne', delta_pos.ne'] <;> ring

theorem scaled_epsilon (p : ProblemParameters) : valueScale p * spaceScale p * delta = p.epsilon := by
  unfold valueScale spaceScale
  field_simp [p.L_pos.ne', p.epsilon_pos.ne', individualConstant_pos.ne', delta_pos.ne'] <;> ring

theorem diameter_mul_spaceScale (p : ProblemParameters) :
    p.diameter * spaceScale p = 2 * (dimensionlessB p / diameterThreshold) := by
  unfold spaceScale dimensionlessB diameterThreshold
  field_simp [p.epsilon_pos.ne', individualConstant_pos.ne', delta_pos.ne'] <;> ring

theorem scaled_diameter_le (p : ProblemParameters) (hn : 65536 ≤ (p.n : ℝ))
    (hB : diameterThreshold ≤ dimensionlessB p) : (2 * publicRadius p) / spaceScale p ≤ p.diameter := by
  apply (div_le_iff₀ (spaceScale_pos p)).mpr
  rw [diameter_mul_spaceScale]
  exact mul_le_mul_of_nonneg_left (publicRadius_bounds p hn hB).2.1 (by norm_num)

theorem normalized_gap_bound (p : ProblemParameters) (hn : 65536 ≤ (p.n : ℝ))
    (hB : diameterThreshold ≤ dimensionlessB p)
    (hA : 400 * gapScale * publicRatio p ≤ dimensionlessA p) :
    gapScale * (normalizedParameters p hn hB).gap ≤ dimensionlessA p := by
  have hq := (publicRatio_bounds p hn hB).1
  have ht := stageCount_bounds gapScale_pos (by linarith : 1 ≤ publicRatio p) hA
  have he : publicStageIndex p + 1 = publicStageCount p := ht.2.2.2
  change gapScale * (1 + 91 * (publicStageIndex p + 1 : ℕ) * publicRatio p) ≤ _
  rw [he]
  exact ht.2.2.1

theorem scaled_gap_le (p : ProblemParameters) (hn : 65536 ≤ (p.n : ℝ))
    (hB : diameterThreshold ≤ dimensionlessB p)
    (hA : 400 * gapScale * publicRatio p ≤ dimensionlessA p) :
    valueScale p * (normalizedParameters p hn hB).gap ≤ p.gap := by
  have hg := normalized_gap_bound p hn hB hA
  calc
    valueScale p * (normalizedParameters p hn hB).gap =
        (p.epsilon ^ 2 * (gapScale * (normalizedParameters p hn hB).gap)) / p.L := by
      rw [valueScale_eq]
      ring
    _ ≤ (p.epsilon ^ 2 * dimensionlessA p) / p.L :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg (sq_nonneg _)) p.L_pos.le
    _ = p.gap := by
      unfold dimensionlessA
      field_simp [p.epsilon_pos.ne', p.L_pos.ne']

theorem parameters_ext (p q : ProblemParameters) (hn : p.n = q.n) (hL : p.L = q.L)
    (hgap : p.gap = q.gap) (heps : p.epsilon = q.epsilon) (hD : p.diameter = q.diameter) : p = q := by
  cases p
  cases q
  simp_all

theorem scaled_retagged_parameters (p : ProblemParameters) (hn : 65536 ≤ (p.n : ℝ))
    (hB : diameterThreshold ≤ dimensionlessB p) :
    ProblemBounds.parameters
      (ProblemScaling.parameters (normalizedParameters p hn hB) (valueScale p) (spaceScale p)
        (valueScale_pos p) (spaceScale_pos p)) p.gap p.epsilon p.diameter
      p.gap_pos p.epsilon_pos p.diameter_nonneg = p := by
  apply parameters_ext
  · rfl
  · exact scaled_L p
  · rfl
  · rfl
  · rfl

/-- Exact same-budget transfer of the normalized cone lower bound into the
large-gap, large-diameter regime. The normalized lower-bound proof is an
explicit input to this reduction and is supplied by the Haar coupling. -/
theorem lowerBudget_of_normalized (p : ProblemParameters) (hn : 65536 ≤ (p.n : ℝ))
    (hB : diameterThreshold ≤ dimensionlessB p)
    (hA : 400 * gapScale * publicRatio p ≤ dimensionlessA p)
    (hLower : LowerBudgetBound (normalizedParameters p hn hB) .individual
      ((p.n : ℝ) * (publicStageIndex p + 1 : ℕ) / 4096)) :
    LowerBudgetBound p .individual
      (dimensionlessA p * optimizationLower (p.n : ℝ) (dimensionlessB p) /
        (400 * 4096 * gapScale * diameterThreshold)) := by
  have hs := ProblemScaling.lowerBudget_transfer (normalizedParameters p hn hB)
    (valueScale_pos p) (spaceScale_pos p) hLower
  have hsGap : (ProblemScaling.parameters (normalizedParameters p hn hB) (valueScale p) (spaceScale p)
      (valueScale_pos p) (spaceScale_pos p)).gap ≤ p.gap := scaled_gap_le p hn hB hA
  have hsDiam : (ProblemScaling.parameters (normalizedParameters p hn hB) (valueScale p) (spaceScale p)
      (valueScale_pos p) (spaceScale_pos p)).diameter ≤ p.diameter := scaled_diameter_le p hn hB
  have hsEps : p.epsilon ≤ (ProblemScaling.parameters (normalizedParameters p hn hB) (valueScale p) (spaceScale p)
      (valueScale_pos p) (spaceScale_pos p)).epsilon := by
    change p.epsilon ≤ valueScale p * spaceScale p * delta
    rw [scaled_epsilon]
  have hb := ProblemBounds.lowerBudget_transfer _ p.gap_pos p.epsilon_pos p.diameter_nonneg hsGap hsDiam hsEps hs
  rw [scaled_retagged_parameters p hn hB] at hb
  intro T hT
  have ht := stageCount_bounds gapScale_pos (by linarith [(publicRatio_bounds p hn hB).1] : 1 ≤ publicRatio p) hA
  have he : publicStageIndex p + 1 = publicStageCount p := ht.2.2.2
  have hcost := calibrated_budget_bound hn diameterThreshold_ge_one hB gapScale_pos hA
  change _ ≤ (p.n : ℝ) * (publicStageCount p : ℝ) / 4096 at hcost
  rw [← he] at hcost
  exact hcost.trans (hb T hT)

end NCConcave16991.ConeCalibration
