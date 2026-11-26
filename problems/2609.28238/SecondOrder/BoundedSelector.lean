import SecondOrder.BoundedC3
import SecondOrder.ReverseSelectorBounds

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boundedC3_bernoulliMixture (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ)
    (hp : ∀ i, BoundedC3 (p i)) (hV : ∀ w, BoundedC3 (V w)) :
    BoundedC3 (bernoulliMixture p V) := by
  apply boundedC3_finset_sum
  intro w _
  apply BoundedC3.mul _ (hV w)
  apply boundedC3_finset_prod
  intro i _
  cases w i
  · exact (hp i).one_sub
  · exact hp i

theorem boundedC3_reverseBlockSelector {n : ℕ} (p : Fin n → E → ℝ)
    (V : ℕ → HomogeneousBlocks (Fin n) E → ℝ)
    (hp : ∀ i, BoundedC3 (p i)) (hV : ∀ j ≤ n, BoundedC3 (V j)) :
    BoundedC3 (reverseBlockSelector p V) := by
  rw [reverseBlockSelector_eq_mixture]
  exact boundedC3_bernoulliMixture _ _
    (fun i => (hp i).comp_contraction (blockProj i) (blockProj_norm_le_one i))
    (fun w => hV _ (lastSuccess_le w))

end
end SecondOrder
