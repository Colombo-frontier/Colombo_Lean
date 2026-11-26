import Task003Base

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Task003Integration
noncomputable section

/-- Conditioning commutes with a measurable pushforward when the event is pulled back. -/
theorem map_cond_preimage {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (g : A → B) (hg : Measurable g) (s : Set B)
    (hs : MeasurableSet s) :
    (ProbabilityTheory.cond μ (g ⁻¹' s)).map g =
      ProbabilityTheory.cond (μ.map g) s := by
  ext t ht
  rw [Measure.map_apply hg ht, ProbabilityTheory.cond_apply (hs.preimage hg),
    ProbabilityTheory.cond_apply hs, Measure.map_apply hg hs,
    Measure.map_apply hg (hs.inter ht)]
  rfl

theorem truncation_preimage (d : ℕ) :
    (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹'
        Metric.closedBall 0 (2 * Real.sqrt d) = PaperTruncatedGaussianRows.truncEvent d := by
  ext b
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
    PaperTruncatedGaussianRows.truncEvent, Set.mem_setOf_eq]
  change ‖WithLp.toLp 2 b‖ ≤ 2 * Real.sqrt (d : ℝ) ↔
    PaperTruncatedGaussianRows.normSq b ≤ 4 * (d : ℝ)
  have hnorm : ‖(WithLp.toLp 2 b : EuclideanSpace ℝ (Fin d))‖ ^ 2 =
      PaperTruncatedGaussianRows.normSq b := by
    simpa [PaperTruncatedGaussianRows.normSq] using
      (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin d)))
  constructor <;> intro h
  · nlinarith [Real.sq_sqrt (Nat.cast_nonneg d),
      norm_nonneg (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin d)), Real.sqrt_nonneg (d : ℝ)]
  · nlinarith [Real.sq_sqrt (Nat.cast_nonneg d),
      norm_nonneg (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin d)), Real.sqrt_nonneg (d : ℝ)]

theorem truncatedLaw_to_euclidean (d : ℕ) :
    (PaperTruncatedGaussianRows.truncatedLaw d).map
        (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) =
      ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin d)))
        (Metric.closedBall 0 (2 * Real.sqrt d)) := by
  have hg : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) := by
    fun_prop
  have hp : (PaperHiddenSpikeTails.noiseLaw d 1).map
      (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
    exact map_pi_eq_stdGaussian
  rw [PaperTruncatedGaussianRows.truncatedLaw, ← truncation_preimage]
  rw [map_cond_preimage _ _ hg _ measurableSet_closedBall, hp]

end
end Task003Integration
