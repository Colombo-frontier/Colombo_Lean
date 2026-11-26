import Matvec.DilationSpectrum

/-! Concrete Euclidean Schur-complement least-stretch comparison. -/
namespace Matvec
noncomputable section
open Matrix
open scoped Matrix

def euclideanSumJoin {q k : ℕ} (u : EuclideanSpace ℝ (Fin q))
    (v : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin q ⊕ Fin k) :=
  (WithLp.equiv 2 ((Fin q ⊕ Fin k) → ℝ)).symm (Sum.elim (u : Fin q → ℝ) (v : Fin k → ℝ))

theorem euclideanSumJoin_norm_sq {q k : ℕ} (u : EuclideanSpace ℝ (Fin q))
    (v : EuclideanSpace ℝ (Fin k)) : ‖euclideanSumJoin u v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  simp only [euclidean_norm_sq, Fintype.sum_sum_type]
  rfl

def blockEuclideanMap {q k : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (B : Matrix (Fin q) (Fin k) ℝ) (C : Matrix (Fin k) (Fin q) ℝ)
    (Z : Matrix (Fin k) (Fin k) ℝ) :
    EuclideanSpace ℝ (Fin q ⊕ Fin k) →L[ℝ] EuclideanSpace ℝ (Fin q ⊕ Fin k) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.fromBlocks A B C Z))

theorem schur_leastStretch {q k : ℕ} (hk : 0 < k)
    (A Ainv : Matrix (Fin q) (Fin q) ℝ) (B : Matrix (Fin q) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin q) ℝ) (Z : Matrix (Fin k) (Fin k) ℝ)
    (hA : A * Ainv = 1) :
    leastStretch (blockEuclideanMap A B C Z) ≤
      leastStretch (LowRank.matrixEuclideanMap (Z - C * Ainv * B)) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  apply leastStretch_le_of_lifts _ _ (exists_unit_vector (E := EuclideanSpace ℝ (Fin k)))
  intro z hz
  let u : EuclideanSpace ℝ (Fin q) :=
    (WithLp.equiv 2 (Fin q → ℝ)).symm (-(Ainv *ᵥ (B *ᵥ (z : Fin k → ℝ))))
  let w := euclideanSumJoin u z
  refine ⟨w, ?_, ?_⟩
  · have h := euclideanSumJoin_norm_sq u z
    rw [hz] at h
    change ‖w‖ ^ 2 = _ at h
    nlinarith [sq_nonneg ‖u‖, norm_nonneg w]
  · have himage : blockEuclideanMap A B C Z w =
        euclideanSumJoin (0 : EuclideanSpace ℝ (Fin q))
          (LowRank.matrixEuclideanMap (Z - C * Ainv * B) z) := by
      apply (WithLp.equiv 2 ((Fin q ⊕ Fin k) → ℝ)).injective
      exact schur_lift A Ainv B C Z hA (z : Fin k → ℝ)
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [himage, euclideanSumJoin_norm_sq, norm_zero, zero_pow (by decide), zero_add]

end
end Matvec
