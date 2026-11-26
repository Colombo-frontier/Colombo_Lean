import GradientHessian.GaussianFrobeniusLaw

/-! Turning Frobenius coordinates into a matrix operator is a continuous
linear contraction. This gives the exact Lipschitz constant for singular values. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open Matrix MeasureTheory GaussianHilbert
open scoped Matrix BigOperators InnerProductSpace

def frobeniusOperator (a b : ℕ) : FrobeniusSpace a b →L[ℝ]
    (EuclideanSpace ℝ (Fin b) →L[ℝ] EuclideanSpace ℝ (Fin a)) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap).comp
      (matrixEntries a b).toLinearMap)

theorem frobeniusOperator_apply (a b : ℕ) (z : FrobeniusSpace a b) :
    frobeniusOperator a b z=LowRank.matrixEuclideanMap (matrixEntries a b z) := rfl

theorem euclidean_norm_square_sum {I : Type*} [Fintype I] (x : EuclideanSpace ℝ I) :
    ‖x‖^2=∑ i,x i^2 := by
  simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,pow_two] using
    (real_inner_self_eq_norm_sq x).symm

theorem frobeniusOperator_pointwise_bound (a b : ℕ) (z : FrobeniusSpace a b) :
    ‖frobeniusOperator a b z‖≤‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg z)
  intro u
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg z) (norm_nonneg u))).mp
  rw [mul_pow,euclidean_norm_square_sum,euclidean_norm_square_sum,euclidean_norm_square_sum,
    Fintype.sum_prod_type]
  change (∑ i,(∑ j,z (i,j)*u j)^2)≤(∑ i,∑ j,z (i,j)^2)*(∑ j,u j^2)
  calc
    _ ≤ ∑ i,(∑ j,z (i,j)^2)*(∑ j,u j^2) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => z (i,j)) (fun j => u j)
    _ = _ := (Finset.sum_mul ..).symm

theorem norm_frobeniusOperator_le_one (a b : ℕ) : ‖frobeniusOperator a b‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  simpa only [one_mul] using frobeniusOperator_pointwise_bound a b z

theorem frobeniusOperator_lipschitz (a b : ℕ) : LipschitzWith 1 (frobeniusOperator a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one,one_mul,dist_eq_norm,map_sub] using
    frobeniusOperator_pointwise_bound a b (x-y)

end GradientHessian.GaussianConcentration
