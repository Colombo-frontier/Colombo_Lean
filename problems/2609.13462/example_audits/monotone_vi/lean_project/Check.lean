import Mathlib
#check LipschitzWith.norm
#check LipschitzWith.norm_sub_norm
#check LipschitzWith.pow
#check LocallyLipschitz.norm
#check LocallyLipschitz.pow
#check LocallyLipschitz.smul
#check LocallyLipschitz.mul
#check LocallyLipschitz.add
#check LipschitzWith.locallyLipschitz
#check LipschitzWith.comp
#check lipschitzWith_norm
#check LipschitzWith.smul
#check Continuous.locallyLipschitz
#check ContDiff.locallyLipschitz
#check contDiff_norm_rpow
#check IsCompact.isBounded
#check IsBounded.subset_closedBall
#check IsCompact.exists_bound_of_continuousOn
#check LocallyLipschitz.pow
#check LocallyLipschitz.const_smul
#check LocallyLipschitz.sub
#check LocallyLipschitz.add
#check lipschitzWith_one_norm
#check ContinuousMultilinearMap.contDiff
#check contDiff_pow
#check le_tsub_iff_right
#check le_tsub_iff_left
#check tsub_le_tsub_right
#check Nat.factorial_pred
#check Nat.factorial_succ
#check continuous_iff_seqContinuous
#check SeqContinuous
#check tendsto_iff_dist_tendsto_zero
#check Metric.tendsto_atTop
#check not_tendsto_iff_exists_eventually_le
#check Filter.not_tendsto
#check hasFDerivAt_norm
#check HasFDerivAt.smul
#check HasFDerivAt.smul_const
#check ContinuousLinearMap.smulRight
example (p : ℕ) (hp : 2 ≤ p) : (1 : WithTop ℕ∞) ≤ (p : WithTop ℕ∞) - 1 := by
  have hp' : (2 : WithTop ℕ∞) ≤ (p : WithTop ℕ∞) := by exact_mod_cast hp
  calc
    1 = (2 : WithTop ℕ∞) - 1 := by norm_num
    _ ≤ (p : WithTop ℕ∞) - 1 := tsub_le_tsub_right hp' _
example (p : ℕ) (hp : 2 ≤ p) : (1 : WithTop ℕ∞) < (p : WithTop ℕ∞) := by
  apply WithTop.coe_lt_coe.mpr
  exact ENat.coe_lt_coe.mpr (by omega)
