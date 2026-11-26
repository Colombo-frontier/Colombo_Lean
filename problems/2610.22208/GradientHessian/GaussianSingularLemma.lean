import GradientHessian.GaussianSingularMeans
import GradientHessian.GaussianSingularConcentration

/-! The manuscript's extreme singular-value tails under the literal
independent-entry standard Gaussian matrix law. The smallest singular value
is its attained variational definition on the Euclidean unit sphere. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped Matrix

theorem matrixEuclideanMap_continuous (a b : ℕ) :
    Continuous (fun G : Matrix (Fin a) (Fin b) ℝ => LowRank.matrixEuclideanMap G) := by
  have h := (frobeniusOperator a b).continuous.comp (matrixVector a b).continuous
  convert h using 1

theorem iidMatrix_largestExpansion_tail (a b : ℕ) [NeZero a] [NeZero b]
    {t : ℝ} (ht : 0 ≤ t) :
    (LowRank.iidMatrixLaw a b 1).real
      {G | Real.sqrt a + Real.sqrt b + t < ‖LowRank.matrixEuclideanMap G‖} ≤
      Real.exp (-t^2/2) := by
  have hm : MeasurableSet
      {G : Matrix (Fin a) (Fin b) ℝ | Real.sqrt a + Real.sqrt b + t < ‖LowRank.matrixEuclideanMap G‖} :=
    measurableSet_lt measurable_const (matrixEuclideanMap_continuous a b).norm.measurable
  rw [← matrixEntries_gaussian_law a b,map_measureReal_apply (matrixEntries a b).continuous.measurable hm]
  exact gaussian_largestExpansion_tail (FrobeniusSpace a b) (frobeniusOperator a b)
    (norm_frobeniusOperator_le_one a b) (gaussian_largestExpansion_mean a b) ht

theorem iidMatrix_leastExpansion_tail (a b : ℕ) [NeZero a] [NeZero b]
    {t : ℝ} (ht : 0 ≤ t) :
    (LowRank.iidMatrixLaw a b 1).real
      {G | leastExpansion (LowRank.matrixEuclideanMap G) < Real.sqrt ((a : ℝ)-1) - Real.sqrt b - t} ≤
      Real.exp (-t^2/2) := by
  have hm : MeasurableSet
      {G : Matrix (Fin a) (Fin b) ℝ |
        leastExpansion (LowRank.matrixEuclideanMap G) < Real.sqrt ((a : ℝ)-1) - Real.sqrt b - t} :=
    measurableSet_lt (leastExpansion_lipschitz.continuous.comp
      (matrixEuclideanMap_continuous a b)).measurable measurable_const
  rw [← matrixEntries_gaussian_law a b,map_measureReal_apply (matrixEntries a b).continuous.measurable hm]
  exact gaussian_leastExpansion_tail (FrobeniusSpace a b) (frobeniusOperator a b)
    (norm_frobeniusOperator_le_one a b) (gaussian_leastExpansion_mean a b) ht

/-- Exact scope and constants of manuscript `lem:singular`. -/
theorem gaussian_extreme_singular_values (a b : ℕ) (hab : b ≤ a) (hb : 1 ≤ b)
    {t : ℝ} (ht : 0 ≤ t) :
    (LowRank.iidMatrixLaw a b 1).real
      {G | Real.sqrt a + Real.sqrt b + t < ‖LowRank.matrixEuclideanMap G‖} ≤ Real.exp (-t^2/2) ∧
    (LowRank.iidMatrixLaw a b 1).real
      {G | leastExpansion (LowRank.matrixEuclideanMap G) < Real.sqrt ((a : ℝ)-1) - Real.sqrt b - t} ≤
      Real.exp (-t^2/2) := by
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  exact ⟨iidMatrix_largestExpansion_tail a b ht,iidMatrix_leastExpansion_tail a b ht⟩

end GradientHessian.GaussianConcentration
