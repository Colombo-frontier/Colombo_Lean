import LowRank.GaussianRangeRecovery
import LowRank.StoppingGramSimulation
import LowRank.ProjectorRank

/-! Exact Gaussian range recovery remains impossible for adaptive stopping
policies with fewer queries than Gaussian columns and a proper-rank output. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem gram_projector_residual_zero_iff {d k : ℕ}
    (X : Matrix (Fin d) (Fin k) ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (hP : Pᵀ = P) :
    (X * Xᵀ) * (1 - P) = 0 ↔ (1 - P) * X = 0 := by
  have h := Matrix.self_mul_conjTranspose_mul_eq_zero X (1 - P)
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [h, ← Matrix.transpose_eq_zero]
  simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_transpose, hP]

theorem stoppingGram_exact_containment_ae (r s n : ℕ) (hs : 0 < s)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (policy : BoundedTwoSidedPolicy (r + n)
      (Matrix (Fin (r + n)) (Fin (r + n)) ℝ) n S) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      (1 - runBoundedTwoSided (r + n) n policy (p.2 * p.2ᵀ) p.1) * p.2 =
        (0 : Matrix (Fin (r + n)) (Fin (s + n)) ℝ) →
        runBoundedTwoSided (r + n) n policy (p.2 * p.2ᵀ) p.1 = 1 := by
  have h := ambientOracle_exact_containment_ae r s n hs ν
    (padSymmetricPolicy (r + n) n policy) hv (readPaddedSymmetricOutput (r + n) n policy)
    (measurable_readPaddedSymmetricOutput _ _ policy)
  filter_upwards [h] with p hp
  have hsim := padSymmetricPolicy_simulates (r + n) n policy (p.2 * p.2ᵀ)
    (by simp only [Matrix.transpose_mul, Matrix.transpose_transpose]) p.1
  simpa only [runAmbientGram, hsim] using hp

theorem stoppingGram_no_exact_range_ae (r s n k : ℕ) (hs : 0 < s) (hk : k < r + n)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (policy : BoundedTwoSidedPolicy (r + n)
      (Matrix (Fin (r + n)) (Fin (r + n)) ℝ) n S)
    (hout : policy.Outputs (r + n) (fun P => IsOrthogonalProjector P ∧ P.rank = k) n)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      (p.2 * p.2ᵀ) * (1 - runBoundedTwoSided (r + n) n policy (p.2 * p.2ᵀ) p.1) ≠ 0 := by
  filter_upwards [stoppingGram_exact_containment_ae r s n hs ν policy hv] with p hp
  obtain ⟨hP, hrank⟩ := runBoundedTwoSided_property (r + n) n policy _ hout (p.2 * p.2ᵀ) p.1
  intro he
  have hidentity := hp ((gram_projector_residual_zero_iff p.2 _ hP.symmetric).mp he)
  rw [hidentity, Matrix.rank_one, Fintype.card_fin] at hrank
  omega

end
end LowRank
