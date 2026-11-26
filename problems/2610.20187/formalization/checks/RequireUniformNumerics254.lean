import RationalProjectionError254
import RationalMasterRegret254

open scoped BigOperators
open Paper254
def testRoundedWeights : Fin 3→ℚ :=
  rationalMasterUpdate 8 {0,1} {1,2} ![1/3,2/3,0] ![1/10,-1/5,0] ![0,0,1] (1/4)
#eval decide ((∑ j,testRoundedWeights j)=1 ∧ testRoundedWeights 0=0 ∧
  0<testRoundedWeights 1 ∧ 0<testRoundedWeights 2)
#eval decide ((1/4:ℚ)/(1+3*2/(2:ℚ)^8)≤testRoundedWeights 2)

#print axioms Paper254.inverse_quadratic_upper_of_lower
#print axioms Paper254.rationalTiltCovariance_upper
#print axioms Paper254.rationalTiltCovariance_spectrum
#print axioms Paper254.uniform_history_scalar_guards
#print axioms Paper254.uniform_history_spectral_guard
#print axioms Paper254.uniformHistoryParameters_guards
#print axioms Paper254.rationalHistoryStep_preserves
#print axioms Paper254.rationalHistoryRun_invariant
#print axioms Paper254.rationalHistoryRun_uniform
#print axioms Paper254.rationalHistoryRun_causal
#print axioms Paper254.scalar_matrix_quadratic
#print axioms Paper254.rationalHistoryInitial_invariant
#print axioms Paper254.rationalHistoryRun_from_initial
#print axioms Paper254.rationalLiveMass_bounds
#print axioms Paper254.rationalLiveSoftmax_spec
#print axioms Paper254.rationalPruneShare_spec
#print axioms Paper254.rationalLiveSoftmax_zero_lower
#print axioms Paper254.rationalRoundedPruneShare_spec
#print axioms Paper254.rationalMasterUpdate_spec
#print axioms Paper254.rationalMasterUpdate_log_overhead
#print axioms Paper254.master_rounding_precision
#print axioms Paper254.log_relative_survival
#print axioms Paper254.rationalMasterUpdate_regret
#print axioms Paper254.inexact_history_prefix
#print axioms Paper254.inverse_min_clip
#print axioms Paper254.PrecisionGaussian.inverse_spectral
#print axioms Paper254.PrecisionGaussian.inverse_eigenvalue_bound
#print axioms Paper254.PrecisionGaussian.floor_inverse_clip
#print axioms Paper254.PrecisionGaussian.floor_covariance_interval
#print axioms Paper254.realMatrix_mulVec
#print axioms Paper254.rationalTiltGaussian_precision
#print axioms Paper254.rationalTiltGaussian_mean
#print axioms Paper254.rationalNextCovariance_exact_floor_error
#print axioms Paper254.covariance_inverse_norm_bound
#print axioms Paper254.rationalFloor_precision_error
#print axioms Paper254.rationalHistoryStep_mean_error
