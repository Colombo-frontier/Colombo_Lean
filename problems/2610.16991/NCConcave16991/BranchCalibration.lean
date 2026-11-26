import NCConcave16991.BranchCalibrationArithmetic
import NCConcave16991.ProblemDiameterCalibration

/-! # Exact public high-diameter transfer from the normalized branch family

The only input here is the actual normalized branch randomized lower theorem;
all parameter selection, floor estimates and same-budget transfers are proved.
-/

noncomputable section

namespace NCConcave16991.BranchCalibration

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

theorem high_diameter_lower_from_normalized {c : ℝ} (hc : 0 < c)
    (hRaw : ∀ (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (m : ℕ),
      LowerBudgetBound (GlobalHardEuclidean.paperParameters n hn M hM m) .individual
        (c * (n : ℝ) * (M : ℝ) * (m + 1 : ℕ)))
    (p : ProblemParameters) (hA : 4 * gapScale ≤ dimensionlessA p)
    (hB : 4 * diameterScale * (p.n : ℝ) ^ (1 / 4 : ℝ) ≤ dimensionlessB p) :
    LowerBudgetBound p .individual
      (c / (16 * gapScale * diameterScale) * dimensionlessA p *
        (p.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB p) := by
  let M := macroCount (dimensionlessA p)
  let m := chainIndex p.n (dimensionlessB p)
  have hM : 0 < M := by have hh := (macroCount_bounds hA).1; omega
  let source := GlobalHardEuclidean.paperParameters p.n p.n_pos M hM m
  have hRawA : dimensionlessA source ≤ dimensionlessA p := by
    rw [paperParameters_A]
    exact (macroCount_bounds hA).2.2
  have hRawB : dimensionlessB source ≤ dimensionlessB p := by
    rw [paperParameters_B]
    exact (chainCount_bounds p.n_pos hB).2.2.2
  have hLower := ProblemCalibration.diameter_lower_transfer source p rfl hRawA hRawB
    (hRaw p.n p.n_pos M hM m)
  have hcost := calibrated_branch_cost p.n_pos hc.le hA hB
  intro N hN
  exact hcost.trans (hLower N hN)

end NCConcave16991.BranchCalibration
