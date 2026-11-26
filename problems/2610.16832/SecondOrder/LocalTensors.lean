import SecondOrder.BlockProjection

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

variable {J I : Type*} [Fintype J] [Fintype I] (E : J → Type*)
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (S : I → Finset J)

def localTensorSum {k : ℕ}
    (T : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin k => LocalBlockSpace E (S i)) F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => BlockSpace E) F :=
  ∑ i, (T i).compContinuousLinearMap (fun _ => blockRestrict E (S i))

theorem localTensorSum_apply {k : ℕ}
    (T : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin k => LocalBlockSpace E (S i)) F)
    (v : Fin k → BlockSpace E) :
    localTensorSum E S T v = ∑ i, T i (fun j => blockRestrict E (S i) (v j)) := by
  simp [localTensorSum, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

variable (r : ℕ) (hr : ∀ j, (Finset.univ.filter (fun i => j ∈ S i)).card ≤ r)

include hr

/-- A sum of local bilinear forms has norm at most r times the local norm bound. -/
theorem localTensorSum_two_bound
    (T : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin 2 => LocalBlockSpace E (S i)) F)
    {M : ℝ} (hM : 0 ≤ M) (hT : ∀ i, ‖T i‖ ≤ M) : ‖localTensorSum E S T‖ ≤ (r:ℝ)*M := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg r) hM)
  intro v
  rw [localTensorSum_apply]
  calc
    _ ≤ ∑ i, ‖T i (fun j => blockRestrict E (S i) (v j))‖ := norm_sum_le _ _
    _ ≤ ∑ i, M*(‖blockRestrict E (S i) (v 0)‖*‖blockRestrict E (S i) (v 1)‖) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Fin.prod_univ_two] using ContinuousMultilinearMap.le_of_opNorm_le
        (hT i) (fun j => blockRestrict E (S i) (v j))
    _ = M*(∑ i, ‖blockRestrict E (S i) (v 0)‖*‖blockRestrict E (S i) (v 1)‖) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ M*((r:ℝ)*‖v 0‖*‖v 1‖) :=
      mul_le_mul_of_nonneg_left (blockRestrict_cross_sum E S r hr (v 0) (v 1)) hM
    _ = _ := by rw [Fin.prod_univ_two]; ring

/-- The third direction is controlled by the contraction of each restriction;
the other two directions use the same overlap/Cauchy–Schwarz argument. -/
theorem localTensorSum_three_bound
    (T : ∀ i, ContinuousMultilinearMap ℝ (fun _ : Fin 3 => LocalBlockSpace E (S i)) F)
    {M : ℝ} (hM : 0 ≤ M) (hT : ∀ i, ‖T i‖ ≤ M) : ‖localTensorSum E S T‖ ≤ (r:ℝ)*M := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg r) hM)
  intro v
  rw [localTensorSum_apply]
  calc
    _ ≤ ∑ i, ‖T i (fun j => blockRestrict E (S i) (v j))‖ := norm_sum_le _ _
    _ ≤ ∑ i, M*(‖blockRestrict E (S i) (v 0)‖*‖blockRestrict E (S i) (v 1)‖*
        ‖blockRestrict E (S i) (v 2)‖) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Fin.prod_univ_three] using ContinuousMultilinearMap.le_of_opNorm_le
        (hT i) (fun j => blockRestrict E (S i) (v j))
    _ = M*(∑ i, ‖blockRestrict E (S i) (v 0)‖*‖blockRestrict E (S i) (v 1)‖*
        ‖blockRestrict E (S i) (v 2)‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ M*((r:ℝ)*‖v 0‖*‖v 1‖*‖v 2‖) :=
      mul_le_mul_of_nonneg_left (blockRestrict_triple_sum E S r hr (v 0) (v 1) (v 2)) hM
    _ = _ := by rw [Fin.prod_univ_three]; ring

end
end SecondOrder
