import LowRank.BoundedRectangularPolicy
import LowRank.SchattenContinuity

/-! The actual relative Schatten success event for a rectangular policy
returning k columns. Its joint measurability includes both the unknown
matrix and the independent random seed. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u

def rectangularSchattenSuccess {a b k n : ℕ} {S : Type u} [MeasurableSpace S]
    (p ε : ℝ) (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S)
    (A : Matrix (Fin a) (Fin b) ℝ) : Set S :=
  {seed | let Z := runBoundedRectangular a b n policy A seed
    schattenNorm p (A * (1 - Z * Zᵀ)) ≤ (1 + ε) * optimalSchattenNorm p A k}

theorem measurableSet_rectangularSchattenSuccess_joint {a b k n : ℕ}
    (hk : k ≤ b) {p : ℝ} (hp : 0 < p) (ε : ℝ)
    {S : Type u} [MeasurableSpace S]
    (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S) :
    MeasurableSet {x : Matrix (Fin a) (Fin b) ℝ × S |
      x.2 ∈ rectangularSchattenSuccess p ε policy x.1} := by
  have hZ := measurable_runBoundedRectangular a b n policy
  have hr : Measurable (fun x : Matrix (Fin a) (Fin b) ℝ × S =>
      let Z := runBoundedRectangular a b n policy x.1 x.2
      x.1 * (1 - Z * Zᵀ)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.transpose_apply]
    apply Finset.measurable_sum
    intro l _
    apply ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp measurable_fst)).mul
    apply measurable_const.sub
    apply Finset.measurable_sum
    intro r _
    exact ((measurable_pi_apply r).comp ((measurable_pi_apply l).comp hZ)).mul
      ((measurable_pi_apply r).comp ((measurable_pi_apply j).comp hZ))
  have hl := (continuous_schattenNorm a b hp).measurable.comp hr
  have hu : Measurable (fun x : Matrix (Fin a) (Fin b) ℝ × S =>
      (1 + ε) * optimalSchattenNorm p x.1 k) :=
    measurable_const.mul ((continuous_optimalSchattenNorm a b k hk hp).measurable.comp measurable_fst)
  exact measurableSet_le hl hu

theorem measurableSet_rectangularSchattenSuccess {a b k n : ℕ}
    (hk : k ≤ b) {p : ℝ} (hp : 0 < p) (ε : ℝ)
    {S : Type u} [MeasurableSpace S]
    (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S)
    (A : Matrix (Fin a) (Fin b) ℝ) :
    MeasurableSet (rectangularSchattenSuccess p ε policy A) := by
  have h : Measurable (fun seed : S => (A, seed)) := measurable_const.prodMk measurable_id
  have hset := measurableSet_rectangularSchattenSuccess_joint
    (a := a) (b := b) (k := k) (n := n) (S := S) hk hp ε policy
  change MeasurableSet ((fun seed : S => (A, seed)) ⁻¹'
    {x : Matrix (Fin a) (Fin b) ℝ × S |
      x.2 ∈ rectangularSchattenSuccess (n := n) p ε policy x.1})
  exact MeasurableSet.preimage hset h

end
end LowRank
