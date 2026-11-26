import NCConcave16991.BranchCalibration
import NCConcave16991.DenseSmoothBaselineLower
import NCConcave16991.ReplicatedEnvelope
import NCConcave16991.HeadlineFromLower

/-! # Public calibration from the normalized branch lower bound

The smooth and cone randomized lower bounds are proved inputs. This reduction
calibrates a normalized unrestricted randomized branch lower theorem, proved
concretely in `BranchRandomizedLower`, to the full public main statements.
-/

noncomputable section

open scoped ENNReal

namespace NCConcave16991

def NormalizedBranchLowerSpecification : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (m : ℕ),
    LowerBudgetBound (GlobalHardEuclidean.paperParameters n hn M hM m) .individual
      (c * (n : ℝ) * (M : ℝ) * (m + 1 : ℕ))

theorem complexity_lower_of_budget_lower {p : ProblemParameters} {mode : SmoothnessClass} {b : ℝ}
    (h : LowerBudgetBound p mode b) : ENNReal.ofReal b ≤ oracleComplexity p mode := by
  unfold oracleComplexity
  apply le_iInf
  intro N
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (h N.val N.property)

theorem theorem33_of_normalized_branch (hRaw : NormalizedBranchLowerSpecification) :
    Theorem33Specification := by
  obtain ⟨c,hc,hRaw⟩ := hRaw
  have hg := BranchCalibration.gapScale_pos
  have hd := BranchCalibration.diameterScale_pos
  have hBhd : 1 ≤ 4 * BranchCalibration.diameterScale := by
    have hs : 1 ≤ Real.sqrt 3 := by simpa using Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 3)
    unfold BranchCalibration.diameterScale
    nlinarith
  have hHigh := BranchCalibration.high_diameter_lower_from_normalized hc hRaw
  have hSmooth : ∀ p : ProblemParameters, 2 ≤ dimensionlessA p →
      LowerBudgetBound p .individual ((1 / DenseSmoothCalibration.baselineDenominator) *
        ((p.n : ℝ) + dimensionlessA p * (p.n : ℝ) ^ (1 / 2 : ℝ))) := by
    intro p hA N hN
    have hh := DenseSmoothCalibration.smooth_baseline_lower p hA N hN
    rw [Real.sqrt_eq_rpow] at hh
    convert hh using 1 <;> ring
  obtain ⟨Arep,crep,hArep,hcrep,hRep⟩ := Replication.diameter_lower_of_high_and_smooth
    (4 * BranchCalibration.gapScale) (4 * BranchCalibration.diameterScale)
    (c / (16 * BranchCalibration.gapScale * BranchCalibration.diameterScale))
    2 (1 / DenseSmoothCalibration.baselineDenominator)
    (by positivity) hBhd (by positivity) (by norm_num)
    (one_div_pos.mpr DenseSmoothCalibration.baselineDenominator_pos) hHigh hSmooth
  let D := ConeCalibration.globalDenominator DenseSmoothCalibration.baselineDenominator
  have hD : 0 < D := ConeCalibration.globalDenominator_pos DenseSmoothCalibration.baselineDenominator_pos
  let c0 := min crep (1 / D)
  refine ⟨max Arep 2,c0,lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right _ _),
    lt_min hcrep (one_div_pos.mpr hD),?_⟩
  intro p hA
  have hA2 : 2 ≤ dimensionlessA p := (le_max_right Arep 2).trans hA
  have hAr : Arep ≤ dimensionlessA p := (le_max_left Arep 2).trans hA
  have hAn := (dimensionlessA_pos p).le
  have hBn := dimensionlessB_nonneg p
  have hclip := clippedDiameter_nonneg (dimensionlessB p)
  have hOptNonneg : 0 ≤ (p.n : ℝ) + dimensionlessA p * optimizationLower (p.n : ℝ) (dimensionlessB p) := by
    unfold optimizationLower
    positivity
  have hDiaNonneg : 0 ≤ (p.n : ℝ) + dimensionlessA p * diameterLower (p.n : ℝ) (dimensionlessB p) := by
    unfold diameterLower
    positivity
  constructor
  · apply complexity_lower_of_budget_lower
    intro N hN
    calc
      _ ≤ (1 / D) * ((p.n : ℝ) + dimensionlessA p * optimizationLower (p.n : ℝ) (dimensionlessB p)) :=
        mul_le_mul_of_nonneg_right (min_le_right crep (1 / D)) hOptNonneg
      _ = ((p.n : ℝ) + dimensionlessA p * optimizationLower (p.n : ℝ) (dimensionlessB p)) / D := by ring
      _ ≤ (N : ℝ) := ConeCalibration.optimization_randomized_lower p hA2 N hN
  · apply complexity_lower_of_budget_lower
    intro N hN
    exact (mul_le_mul_of_nonneg_right (min_le_left crep (1 / D)) hDiaNonneg).trans (hRep p hAr N hN)

theorem theorem31Global_of_normalized_branch (hRaw : NormalizedBranchLowerSpecification) :
    Theorem31GlobalSpecification := theorem31Global_of_theorem33 (theorem33_of_normalized_branch hRaw)

theorem theorem31Piecewise_of_normalized_branch (hRaw : NormalizedBranchLowerSpecification) :
    Theorem31PiecewiseSpecification := theorem31Piecewise_of_theorem33 (theorem33_of_normalized_branch hRaw)

end NCConcave16991
