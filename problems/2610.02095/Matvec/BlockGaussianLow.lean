import Matvec.GaussianShiftCore
import Matvec.SchurLeastStretch
import Matvec.PivotPerturbation
import Matvec.GaussianDistributionBounds
import Matvec.KernelLeastStretch

/-! A dimension-uniform low event for a Gaussian hidden block with arbitrary
visible blocks. Singular pivots are handled by an arbitrarily small visible
perturbation, so no measurable invertible-pivot selector is required. -/

namespace Matvec
open Matrix MeasureTheory LowRank
open scoped Matrix
noncomputable section

theorem blockEuclideanMap_shift {q k : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (B : Matrix (Fin q) (Fin k) ℝ) (C : Matrix (Fin k) (Fin q) ℝ)
    (Z : Matrix (Fin k) (Fin k) ℝ) (δ : ℝ) :
    blockEuclideanMap (A + δ • 1) B C Z - blockEuclideanMap A B C Z =
      visibleBlockShift q k δ := by
  have hm : Matrix.fromBlocks (A + δ • 1) B C Z - Matrix.fromBlocks A B C Z =
      Matrix.fromBlocks (δ • (1 : Matrix (Fin q) (Fin q) ℝ))
        (0 : Matrix (Fin q) (Fin k) ℝ) (0 : Matrix (Fin k) (Fin q) ℝ) 0 := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]
  ext x i
  change (Matrix.fromBlocks (A + δ • 1) B C Z *ᵥ (x : _ → ℝ)) i -
    (Matrix.fromBlocks A B C Z *ᵥ (x : _ → ℝ)) i = _
  rw [← Pi.sub_apply, ← Matrix.sub_mulVec, hm]
  rfl

theorem block_leastStretch_perturbation {q k : ℕ} (hk : 0 < k)
    (A : Matrix (Fin q) (Fin q) ℝ) (B : Matrix (Fin q) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin q) ℝ) (Z : Matrix (Fin k) (Fin k) ℝ) (δ : ℝ) :
    leastStretch (blockEuclideanMap A B C Z) ≤
      leastStretch (blockEuclideanMap (A + δ • 1) B C Z) + |δ| := by
  have hunit : ∃ x : EuclideanSpace ℝ (Fin q ⊕ Fin k), ‖x‖ = 1 :=
    ⟨(EuclideanSpace.basisFun _ ℝ) (Sum.inr ⟨0, hk⟩),
      (EuclideanSpace.basisFun _ ℝ).norm_eq_one _⟩
  have h := leastStretch_sub_le (blockEuclideanMap A B C Z)
    (blockEuclideanMap (A + δ • 1) B C Z) hunit
  rw [norm_sub_rev, blockEuclideanMap_shift] at h
  have hnorm := visibleBlockShift_norm_le q k δ
  linarith

theorem lowRankShiftCore_leastStretch {q ℓ : ℕ} (hℓ : 0 < ℓ)
    (C : Matrix (Fin (q + ℓ)) (Fin q) ℝ) (B : Matrix (Fin q) (Fin (q + ℓ)) ℝ)
    (X : Matrix (Fin (q + ℓ)) (Fin (q + ℓ)) ℝ) :
    leastStretch (matrixEuclideanMap (X - C * B)) ≤
      leastStretch (matrixEuclideanMap (lowRankShiftCore C B X)) := by
  apply kernel_compression_leastStretch hℓ (X - C * B) (shiftRowRotation C)
    (lowRankShiftKernel C B (splitGaussianRows q ℓ (q + ℓ) (shiftRowRotation C * X)).1)
    (lowRankShiftCore C B X) (shiftRowRotation_orthogonal C)
    (lowRankShiftKernel_orthogonal C B _)
  · intro i j
    exact congrFun (congrFun (lowRankShiftCore_annihilation C B X) i) j
  · intro i j
    exact congrFun (congrFun (lowRankShiftCore_bottom C B X) i) j

/-- The lower probability bound is uniform over all three visible blocks,
including singular pivots. Its proof constructs an actual iid Gaussian core. -/
theorem block_gaussian_leastStretch_low (q n : ℕ) (hn : lowEventRank ≤ n)
    (A : Matrix (Fin q) (Fin q) ℝ) (B : Matrix (Fin q) (Fin (q + (n + 1))) ℝ)
    (C : Matrix (Fin (q + (n + 1))) (Fin q) ℝ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    smallBallDensity ^ 2 * a ^ 2 / (64 * lowEventRank) ≤
      (iidMatrixLaw (q + (n + 1)) (q + (n + 1)) 1).real
        {Z | leastStretch (blockEuclideanMap A B C Z) ≤ 2 * a / Real.sqrt (n + 1 : ℝ)} := by
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨δ, hδ, hδsmall, hinv, _⟩ :=
    exists_small_pivot_with_inverse A (div_pos ha hs)
  let C' := C * (A + δ • 1)⁻¹
  let F := lowRankShiftCore C' B
  let μ := iidMatrixLaw (q + (n + 1)) (q + (n + 1)) 1
  haveI : IsProbabilityMeasure μ := iidMatrixLaw_probability _ _ _
  have hF : MeasurePreserving F μ (iidMatrixLaw (n + 1) (n + 1) 1) :=
    lowRankShiftCore_preserving C' B 1
  let E := {D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ |
    leastStretch (matrixEuclideanMap D) ≤ a / Real.sqrt (n + 1 : ℝ)}
  have hE : MeasurableSet E :=
    measurableSet_le (measurable_matrix_leastStretch _ _ (by omega)) measurable_const
  have hpre := hF.measureReal_preimage hE.nullMeasurableSet
  apply (gaussian_leastStretch_low n hn ha ha1).trans
  rw [← hpre]
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono
  intro Z hZ
  have hc := lowRankShiftCore_leastStretch (q := q) (ℓ := n + 1) (by omega) C' B Z
  have hschur := schur_leastStretch (by omega : 0 < q + (n + 1))
    (A + δ • 1) (A + δ • 1)⁻¹ B C Z hinv
  have hpert := block_leastStretch_perturbation (by omega : 0 < q + (n + 1)) A B C Z δ
  rw [abs_of_pos hδ] at hpert
  change leastStretch (matrixEuclideanMap (F Z)) ≤ a / Real.sqrt (n + 1 : ℝ) at hZ
  change leastStretch (matrixEuclideanMap (Z - C * (A + δ • 1)⁻¹ * B)) ≤
    leastStretch (matrixEuclideanMap (F Z)) at hc
  change leastStretch (blockEuclideanMap A B C Z) ≤ _
  have ht : 2 * a / Real.sqrt (n + 1 : ℝ) =
      a / Real.sqrt (n + 1 : ℝ) + a / Real.sqrt (n + 1 : ℝ) := by ring
  rw [ht]
  linarith

end
end Matvec
