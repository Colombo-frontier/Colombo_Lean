import LowRank.GaussianFrobeniusMean
import LowRank.WeightedFilteredApproximation

/-! A joint bound for the tail block times the inverse of Gaussian top
coordinates. The union bound does not require these two blocks to be independent. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem measure_frobeniusSq_mul_tail_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {a b c : ℕ} (B : Ω → Matrix (Fin a) (Fin b) ℝ) (C : Ω → Matrix (Fin b) (Fin c) ℝ)
    {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) :
    μ {x | R * S < frobeniusSq (B x * C x)} ≤
      μ {x | R < frobeniusSq (B x)} + μ {x | S < frobeniusSq (C x)} := by
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro x hx
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra! h
  have hprod := mul_le_mul h.1 h.2 (frobeniusSq_nonneg _) hR
  exact (not_lt_of_ge ((frobeniusSq_mul_le (B x) (C x)).trans hprod)) hx

theorem iidMatrixLaw_startingBlock_factor_tail {a d k s : ℕ}
    (M : Matrix (Fin a) (Fin d) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (hs : k + 2 ≤ s) {R S : ℝ} (hR : 0 < R) (hS : 0 < S) :
    (iidMatrixLaw d s 1) {U | R * S < frobeniusSq ((M * U) * gramRightInverse (Vᵀ * U))} ≤
      ENNReal.ofReal ((s : ℝ) * frobeniusSq M) / ENNReal.ofReal R +
        ENNReal.ofReal ((k : ℝ) / ((s : ℝ) - k - 1)) / ENNReal.ofReal S := by
  exact (measure_frobeniusSq_mul_tail_le (iidMatrixLaw d s 1)
    (fun U => M * U) (fun U => gramRightInverse (Vᵀ * U)) hR.le hS.le).trans
      (add_le_add (iidMatrixLaw_mul_frobeniusSq_tail_le M hR)
        (iidMatrixLaw_compressed_gramRightInverse_tail_le V hV hs hS))

end
end LowRank
