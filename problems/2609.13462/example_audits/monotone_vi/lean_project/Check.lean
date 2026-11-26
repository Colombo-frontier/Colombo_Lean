import Mathlib

/-! API checks for the pinned Mathlib release. Powers and products use smoothness
to obtain local Lipschitz regularity; continuity alone does not imply it. -/
#check lipschitzWith_one_norm
#check norm_sub_norm_le
#check ContDiff.pow
#check LocallyLipschitz.comp
#check ContDiff.locallyLipschitz
#check ContDiff.smul
#check ContDiff.mul
#check LocallyLipschitz.add
#check LipschitzWith.locallyLipschitz
#check LipschitzWith.comp
#check lipschitzWith_one_norm
#check ContDiff.smul_const
#check ContDiff.locallyLipschitz
#check ContDiff.locallyLipschitz
#check contDiff_norm_rpow
#check IsCompact.isBounded
#check Bornology.IsBounded.subset_closedBall
#check IsCompact.exists_bound_of_continuousOn
#check ContDiff.pow
#check ContDiff.const_smul
#check LocallyLipschitz.sub
#check LocallyLipschitz.add
#check lipschitzWith_one_norm
#check ContinuousMultilinearMap.contDiff
#check ContDiff.pow
#check le_tsub_iff_right
#check le_tsub_iff_left
#check tsub_le_tsub_right
#check Nat.mul_factorial_pred
#check Nat.factorial_succ
#check continuous_iff_seqContinuous
#check SeqContinuous
#check tendsto_iff_dist_tendsto_zero
#check Metric.tendsto_atTop
#check Filter.not_tendsto_iff_exists_frequently_notMem
#check Filter.Tendsto.not_tendsto
#check hasFDerivAt_norm_rpow
#check HasFDerivAt.smul
#check HasFDerivAt.smul_const
#check ContinuousLinearMap.smulRight
example (p : ℕ) (hp : 2 ≤ p) : (1 : WithTop ℕ∞) ≤ (p : WithTop ℕ∞) - 1 := by
  change ((1 : ℕ∞) : WithTop ℕ∞) ≤
    ((p : ℕ∞) : WithTop ℕ∞) - ((1 : ℕ∞) : WithTop ℕ∞)
  rw [← WithTop.coe_sub, ← ENat.coe_sub]
  exact WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr (by omega))
example (p : ℕ) (hp : 2 ≤ p) : (1 : WithTop ℕ∞) < (p : WithTop ℕ∞) := by
  apply WithTop.coe_lt_coe.mpr
  exact ENat.coe_lt_coe.mpr (by omega)
