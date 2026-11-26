import NCConcave16991.BranchOracleHaarProbability
import NCConcave16991.BranchOracleGaussianSupport
import NCConcave16991.BranchNormalizedBudget

/-! # The unrestricted randomized branch lower bound under the actual static Haar law -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.BranchOracle

open GlobalHard GlobalHardEuclidean MixedHaar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 6000
set_option maxSynthPendingDepth 32
set_option backward.isDefEq.respectTransparency true

def branchAmbientDimension (n M m budget : ℕ) : ℕ :=
  wordAmbientDimension n (M * (m + 1)) (fullMixedCostK M m budget) (fullMixedCostK M m budget) releaseThreshold

theorem branchAmbientDimension_pos (n M m budget : ℕ) : 0 < branchAmbientDimension n M m budget :=
  wordAmbientDimension_pos _ _ _ _ _

theorem branch_haar_bad_probability (n M m : ℕ) [NeZero n] (hn : 0 < n) (hM : 0 < M)
    (budget : ℕ)
    {Ω : Type} [MeasurableSpace Ω]
    (P : StaticPolicy (M := M) (m := m) (Space (branchAmbientDimension n M m budget)) hn Ω)
    (seed : Ω)
    (hbudget : budget ≤ BranchOracleBudget.budget (n : ℝ) releaseThreshold (M * (m + 1))) :
    (staticHaarLaw n M m (branchAmbientDimension n M m budget)).real
      {θ | (seed,θ) ∈ haarBadEvent n M m (branchAmbientDimension n M m budget)
        hn (branchAmbientDimension_pos n M m budget) P budget (lastMacro M hM)} ≤ 1 / 6 := by
  apply (haar_bad_bound_of_common_support n M m (branchAmbientDimension n M m budget)
    hn hM (branchAmbientDimension_pos n M m budget) P seed budget hbudget
    (haarRecordedSampler_common_support_ae n M m (branchAmbientDimension n M m budget)
      hn (branchAmbientDimension_pos n M m budget) P seed budget)).trans
  exact wordAmbientDimension_coefficient n (M * (m + 1))
    (fullMixedCostK M m budget) (fullMixedCostK M m budget) releaseThreshold_pos

theorem invalid_branch_budget (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (m budget : ℕ)
    (hbudget : budget ≤ BranchOracleBudget.budget (n : ℝ) releaseThreshold (M * (m + 1))) :
    ¬ ValidBudget (paperParameters n hn M hM m) .individual budget := by
  letI : NeZero n := ⟨hn.ne'⟩
  apply invalid_budget_of_haar_bad_bound n M m (branchAmbientDimension n M m budget)
    hn (branchAmbientDimension_pos n M m budget) hM budget (lastMacro M hM)
  intro Ω _ P seed
  exact branch_haar_bad_probability n M m hn hM budget P seed hbudget

end NCConcave16991.BranchOracle

namespace NCConcave16991

theorem normalized_branch_randomized_lower : NormalizedBranchLowerSpecification :=
  BranchNormalizedBudget.normalized_specification_of_raw_budget BranchOracle.invalid_branch_budget

end NCConcave16991
