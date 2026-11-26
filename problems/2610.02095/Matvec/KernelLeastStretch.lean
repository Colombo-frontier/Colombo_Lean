import Matvec.SchurLeastStretch

/-! Concrete Euclidean kernel-compression least-stretch comparison. -/
namespace Matvec
open Matrix LowRank
open scoped Matrix BigOperators
noncomputable section

theorem toEuclideanLin_norm_of_orthonormal_columns {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (hA : Aᵀ * A = 1) (x : EuclideanSpace ℝ κ) :
    ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [euclidean_norm_sq, euclidean_norm_sq]
  have h := orthogonal_columns_dot A hA (x : κ → ℝ)
  simpa only [dotProduct, pow_two] using h

theorem matrixEuclideanMap_norm_of_orthonormal_columns {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : Aᵀ * A = 1)
    (x : EuclideanSpace ℝ (Fin n)) : ‖matrixEuclideanMap A x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := orthogonal_columns_dot A hA (x : Fin n → ℝ)
  simpa only [← euclidean_dot_self, matrixEuclideanMap_apply] using h

theorem kernel_compression_leastStretch {q ℓ : ℕ} (hℓ : 0 < ℓ)
    (M O : Matrix (Fin (q + ℓ)) (Fin (q + ℓ)) ℝ)
    (V : Matrix (Fin (q + ℓ)) (Fin ℓ) ℝ) (D : Matrix (Fin ℓ) (Fin ℓ) ℝ)
    (hO : O * Oᵀ = 1) (hV : Vᵀ * V = 1)
    (htop : ∀ i j, (O * M * V) (finSumFinEquiv (Sum.inl i)) j = 0)
    (hbottom : ∀ i j, (O * M * V) (finSumFinEquiv (Sum.inr i)) j = D i j) :
    leastStretch (matrixEuclideanMap M) ≤ leastStretch (matrixEuclideanMap D) := by
  letI : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  have hOt : Oᵀ * O = 1 := Matrix.mul_eq_one_comm.mp hO
  have hnorm (z : EuclideanSpace ℝ (Fin ℓ)) :
      ‖matrixEuclideanMap (O * M * V) z‖ = ‖matrixEuclideanMap D z‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [euclidean_norm_sq, euclidean_norm_sq]
    rw [← (finSumFinEquiv : Fin q ⊕ Fin ℓ ≃ Fin (q + ℓ)).sum_comp]
    rw [Fintype.sum_sum_type]
    change (∑ i : Fin q, (∑ j, (O * M * V) (finSumFinEquiv (Sum.inl i)) j * z j) ^ 2) +
      (∑ i : Fin ℓ, (∑ j, (O * M * V) (finSumFinEquiv (Sum.inr i)) j * z j) ^ 2) =
      ∑ i : Fin ℓ, (∑ j, D i j * z j) ^ 2
    simp only [htop, hbottom, zero_mul, Finset.sum_const_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, zero_add, hbottom]
  apply leastStretch_le_of_lifts _ _ (exists_unit_vector (E := EuclideanSpace ℝ (Fin ℓ)))
  intro z hz
  refine ⟨matrixEuclideanMap V z, ?_, ?_⟩
  · rw [matrixEuclideanMap_norm_of_orthonormal_columns V hV, hz]
  · have h := hnorm z
    rw [matrixEuclideanMap_mul, ContinuousLinearMap.comp_apply,
      matrixEuclideanMap_mul, ContinuousLinearMap.comp_apply,
      matrixEuclideanMap_norm_of_orthonormal_columns O hOt] at h
    exact h

end
end Matvec
