import LowRank.SchattenContinuity
import LowRank.GaussianFrobeniusHardness

/-! Measurable relative-error success against the true rank-k Schatten
optimum for an actual bounded stopping two-sided hard-matrix policy. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section

def boundedOptimalSchattenSuccess (r s n k : ℕ) (p L ε : ℝ)
    {S : Type*} [MeasurableSpace S]
    (policy : BoundedTwoSidedPolicy (r + n) (Matrix (Fin (r + n)) (Fin (r + n)) ℝ) n S) :
    Set (S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :=
  {z | schattenNorm p (hardMatrix L (wishart z.2) * (1 - runBoundedHard r s n L policy z)) ≤
    (1 + ε) * optimalSchattenNorm p (hardMatrix L (wishart z.2)) k}

theorem measurableSet_boundedOptimalSchattenSuccess (r s n k : ℕ) (p L ε : ℝ)
    (hp : 0 < p) (hk : k ≤ r + n)
    {S : Type*} [MeasurableSpace S]
    (policy : BoundedTwoSidedPolicy (r + n) (Matrix (Fin (r + n)) (Fin (r + n)) ℝ) n S) :
    MeasurableSet (boundedOptimalSchattenSuccess r s n k p L ε policy) := by
  have hH : Measurable (fun z : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ =>
      hardMatrix L (wishart z.2)) :=
    (measurable_hardMatrix (r + n) L).comp ((measurable_wishart (r + n) (s + n)).comp measurable_snd)
  have hP := measurable_runBoundedHard r s n L policy
  have hres : Measurable (fun z : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ =>
      hardMatrix L (wishart z.2) * (1 - runBoundedHard r s n L policy z)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mul_apply, Matrix.sub_apply]
    apply Finset.measurable_sum
    intro a _
    exact ((measurable_pi_apply a).comp ((measurable_pi_apply i).comp hH)).mul
      (measurable_const.sub ((measurable_pi_apply j).comp ((measurable_pi_apply a).comp hP)))
  exact measurableSet_le ((continuous_schattenNorm (r + n) (r + n) hp).measurable.comp hres)
    (measurable_const.mul ((continuous_optimalSchattenNorm (r + n) (r + n) k hk hp).measurable.comp hH))

end
end LowRank
