import MatchingBounds1005.EpsilonCalibration

/-! Explicit positive thresholds witnessing every small-parameter requirement. -/
noncomputable section

namespace MatchingBounds1005.EpsilonCalibration

def coreAmplitude (L C : ℝ) : ℝ := min 1 (L / (18 * 8192 * max C 1))

theorem coreAmplitude_pos {L : ℝ} (hL : 0 < L) (C : ℝ) : 0 < coreAmplitude L C := by
  have hD : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  unfold coreAmplitude
  positivity

theorem coreAmplitude_budget {L C : ℝ} (hL : 0 < L) (hC : 0 ≤ C) :
    18 * 8192 * C * coreAmplitude L C ^ 3 ≤ L := by
  let a := coreAmplitude L C
  have ha : 0 < a := coreAmplitude_pos hL C
  have ha1 : a ≤ 1 := min_le_left _ _
  have haδ : a ≤ L / (18 * 8192 * max C 1) := min_le_right _ _
  have hD : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have ha2 : a ^ 2 ≤ 1 := pow_le_one₀ ha.le ha1
  have ha3 : a ^ 3 ≤ a := by nlinarith only [mul_le_mul_of_nonneg_left ha2 ha.le]
  change 18 * 8192 * C * a ^ 3 ≤ L
  calc
    _ ≤ 18 * 8192 * max C 1 * a ^ 3 := by gcongr; exact le_max_left _ _
    _ ≤ 18 * 8192 * max C 1 * a := mul_le_mul_of_nonneg_left ha3 (by positivity)
    _ ≤ _ := by
      have h := (le_div_iff₀ (by positivity : 0 < 18 * 8192 * max C 1)).mp haδ
      nlinarith only [h]

def smallThreshold (a L : ℝ) : ℝ :=
  min 1 (min a (min (1 / (37 * Real.sqrt (8192 * a / L))) (a / (10368 * 8192))))

theorem smallThreshold_pos {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    0 < smallThreshold a L := by
  have hk : 0 < Real.sqrt (8192 * a / L) := Real.sqrt_pos.mpr (by positivity)
  unfold smallThreshold
  positivity

theorem smallThreshold_requirements {a L t : ℝ} (ha : 0 < a) (hL : 0 < L) (ht : 0 < t)
    (htδ : t ≤ smallThreshold a L) :
    t ≤ a ∧ pathScale a L t ≤ 1 / 37 ∧ 10368 * 8192 * t ^ 4 ≤ a := by
  have ht1 : t ≤ 1 := htδ.trans (min_le_left _ _)
  have htrest := htδ.trans (min_le_right _ _)
  have hta : t ≤ a := htrest.trans (min_le_left _ _)
  have htrest' := htrest.trans (min_le_right _ _)
  have htk : t ≤ 1 / (37 * Real.sqrt (8192 * a / L)) := htrest'.trans (min_le_left _ _)
  have hta' : t ≤ a / (10368 * 8192) := htrest'.trans (min_le_right _ _)
  have hk : 0 < Real.sqrt (8192 * a / L) := Real.sqrt_pos.mpr (by positivity)
  have ht3 : t ^ 3 ≤ 1 := pow_le_one₀ ht.le ht1
  have ht4 : t ^ 4 ≤ t := by nlinarith only [mul_le_mul_of_nonneg_left ht3 ht.le]
  refine ⟨hta, ?_, ?_⟩
  · have hf : pathScale a L t = Real.sqrt (8192 * a / L) * t := by
      unfold pathScale curvature
      have heq : 8192 * a * t ^ 2 / L = (8192 * a / L) * t ^ 2 := by ring
      rw [heq, Real.sqrt_mul (by positivity), Real.sqrt_sq ht.le]
    rw [hf]
    have h := (le_div_iff₀ (by positivity : 0 < 37 * Real.sqrt (8192 * a / L))).mp htk
    nlinarith only [h]
  · have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 10368 * 8192)).mp hta'
    nlinarith only [ht4, h]

end MatchingBounds1005.EpsilonCalibration
