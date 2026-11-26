import Matvec.GaussianDistributionBounds
import Matvec.GaussianNormProbability
import Matvec.DilationSpectrum

/-! The normalized Gaussian dilation meets the actual indefinite-solve
spectral promise with arbitrarily high fixed probability. -/
namespace Matvec
open MeasureTheory Matrix LowRank
noncomputable section

theorem gaussian_source_reliable_promise (δ : ℝ) (hδ : 0 < δ) :
    ∃ a K : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 < K ∧ ∀ n : ℕ,
      1 - δ ≤ (iidMatrixLaw (n + 1) (n + 1) 1).real
        {G | (gaussianSourceMap G a).toLinearMap.IsSymmetric ∧
          (∀ w, ‖w‖ ≤ ‖gaussianSourceMap G a w‖) ∧
          ‖gaussianSourceMap G a‖ ≤ K * (n + 1 : ℝ)} := by
  obtain ⟨a, ha, ha1, hhigh⟩ := gaussian_reliable_high_scale (δ / 2) (by positivity)
  obtain ⟨C, hC, hnorm⟩ := gaussian_norm_reliable_constant (δ / 2) (by positivity)
  refine ⟨a, C / a, ha, ha1, by positivity, ?_⟩
  intro n
  let μ := iidMatrixLaw (n + 1) (n + 1) 1
  letI : IsProbabilityMeasure μ := iidMatrixLaw_probability _ _ _
  let E := {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ |
    a / Real.sqrt (n + 1 : ℝ) ≤ leastStretch (matrixEuclideanMap G)}
  let Bad := {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ |
    C * Real.sqrt (n + 1 : ℝ) < ‖matrixEuclideanMap G‖}
  let Good := {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ |
    (gaussianSourceMap G a).toLinearMap.IsSymmetric ∧
      (∀ w, ‖w‖ ≤ ‖gaussianSourceMap G a w‖) ∧
      ‖gaussianSourceMap G a‖ ≤ (C / a) * (n + 1 : ℝ)}
  have hsub : ∀ᵐ G ∂μ, G ∈ E → G ∈ Good ∪ Bad := by
    filter_upwards [iidMatrixLaw_mulVec_injective_ae (n + 1) (n + 1) le_rfl
      (by norm_num : (1 : NNReal) ≠ 0)] with G hG
    intro hE
    by_cases hBad : G ∈ Bad
    · exact Or.inr hBad
    · left
      have hupper : ‖matrixEuclideanMap G‖ ≤ C * Real.sqrt (n + 1 : ℝ) :=
        le_of_not_gt hBad
      have hlo : a / Real.sqrt (n + 1 : ℝ) ≤ leastStretch (matrixEuclideanMap G) := hE
      have hlot : a / Real.sqrt (n + 1 : ℝ) ≤ leastStretch (matrixEuclideanMap G.transpose) := by
        rwa [matrix_leastStretch_transpose G (by omega) hG]
      have hge : ∀ x, (a / Real.sqrt ((n + 1 : ℕ) : ℝ)) * ‖x‖ ≤ ‖matrixEuclideanMap G x‖ := by
        intro x
        simpa only [Nat.cast_add, Nat.cast_one] using
          (mul_le_mul_of_nonneg_right hlo (norm_nonneg x)).trans
            (leastStretch_mul_norm_le (matrixEuclideanMap G) x)
      have hgte : ∀ x, (a / Real.sqrt ((n + 1 : ℕ) : ℝ)) * ‖x‖ ≤ ‖matrixEuclideanMap G.transpose x‖ := by
        intro x
        simpa only [Nat.cast_add, Nat.cast_one] using
          (mul_le_mul_of_nonneg_right hlot (norm_nonneg x)).trans
            (leastStretch_mul_norm_le (matrixEuclideanMap G.transpose) x)
      have hp := gaussianSource_promise G (by omega) a C ha hC.le hge hgte
        (by simpa only [Nat.cast_add, Nat.cast_one] using hupper)
      simpa only [Good, Set.mem_setOf_eq, Nat.cast_add, Nat.cast_one] using hp
  have hm : μ.real E ≤ μ.real Good + μ.real Bad :=
    (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)).trans
      (measureReal_union_le Good Bad)
  have hl : 1 - δ / 2 ≤ μ.real E := hhigh n
  have ht : μ.real Bad ≤ δ / 2 := hnorm n
  change _ ≤ μ.real Good
  linarith

end
end Matvec
