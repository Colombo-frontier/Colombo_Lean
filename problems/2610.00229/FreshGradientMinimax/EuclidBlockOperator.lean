import FreshGradientMinimax.EuclidBlockFamily

/-! The block diagonal lift of a concrete linear map and its actual adjoint. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def euclidBlockMap {m n : ℕ} (k : ℕ) (A : Euclid m →L[ℝ] Euclid n) :
    Euclid (k * m) →L[ℝ] Euclid (k * n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => euclidJoin (fun i => A (euclidBlock i x))
      map_add' := by
        intro x y
        apply euclid_ext_blocks
        intro i
        simp only [euclidBlock_join, map_add]
      map_smul' := by
        intro a x
        apply euclid_ext_blocks
        intro i
        simp only [euclidBlock_join, map_smul, RingHom.id_apply] }

@[simp]
theorem euclidBlockMap_block {k m n : ℕ} (A : Euclid m →L[ℝ] Euclid n)
    (x : Euclid (k * m)) (i : Fin k) :
    euclidBlock i (euclidBlockMap k A x) = A (euclidBlock i x) := by
  change euclidBlock i (euclidJoin (fun j : Fin k => A (euclidBlock j x))) = _
  exact euclidBlock_join _ i

theorem euclidBlockMap_norm {k m n : ℕ} (A : Euclid m →L[ℝ] Euclid n) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ x, ‖A x‖ ≤ C * ‖x‖) (x : Euclid (k * m)) :
    ‖euclidBlockMap k A x‖ ≤ C * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow, euclid_norm_sq_blocks, euclid_norm_sq_blocks x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [euclidBlockMap_block, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hA _) 2

theorem euclidBlockMap_opNorm {m n : ℕ} (k : ℕ) (A : Euclid m →L[ℝ] Euclid n) :
    ‖euclidBlockMap k A‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (euclidBlockMap_norm A (norm_nonneg _) A.le_opNorm)

theorem euclidBlockMap_adjoint {m n : ℕ} (k : ℕ) (A : Euclid m →L[ℝ] Euclid n) :
    (euclidBlockMap k A)† = euclidBlockMap k (A†) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left, euclid_inner_family, euclid_inner_family]
  simp only [euclidBlockMap_block, ContinuousLinearMap.adjoint_inner_left]

end FreshGradientMinimax
