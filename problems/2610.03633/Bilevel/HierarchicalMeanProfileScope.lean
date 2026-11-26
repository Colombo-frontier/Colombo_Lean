import Bilevel.HierarchicalMeanCoercive
import Bilevel.HierarchicalMeanResponse
import Bilevel.HierarchicalMeanGapRate
import Bilevel.ZeroChainProfiles

/-! Scope of the additive hierarchical helpers.

`HierarchicalMean.Parameters` currently uses the capped smooth-transition
activation inherited from `ChiOuter`. The manuscript's earlier fixed
activation is `ZeroChainProfiles.psi`, the uncapped exponential. They are
different functions, as proved below. The Gaussian primitive is exact.

Consequently these additive formula/response/value results certify an
alternate-profile construction. They do not close literal `hier:thm:mean`
or `thm:global`. A source-specific exponential-profile transfer, as well as
the remaining quantitative full regularity bounds, is still required. -/
noncomputable section
namespace Bilevel.HierarchicalMean

theorem source_activation_gt_capped_at_two :
    ChiBoundedChain.psi 2<ZeroChainProfiles.psi 2 := by
  rw [ChiBoundedChain.psi_one (by norm_num)]
  change 1<(if (2:ℝ)≤1/2 then 0 else Real.exp (1-((2*2-1)⁻¹)^2))
  norm_num only [show ¬((2:ℝ)≤1/2) by norm_num,if_false]
  apply Real.one_lt_exp_iff.mpr
  norm_num

theorem source_activation_ne_capped : ZeroChainProfiles.psi≠ChiBoundedChain.psi := by
  intro h
  have hh := source_activation_gt_capped_at_two
  rw [h] at hh
  exact (lt_irrefl _) hh

end Bilevel.HierarchicalMean
