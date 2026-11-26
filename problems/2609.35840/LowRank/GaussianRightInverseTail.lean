import LowRank.GaussianRightInverseMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Quantitative probability bounds for Gaussian right inverses, obtained
from their exact first Frobenius moment. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem measurable_frobeniusSq (a b : ℕ) :
    Measurable (frobeniusSq : Matrix (Fin a) (Fin b) ℝ → ℝ) := by
  unfold frobeniusSq
  fun_prop

theorem measure_frobeniusSq_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {a b : ℕ} (B : Ω → Matrix (Fin a) (Fin b) ℝ) (hB : Measurable B)
    {R : ℝ} (hR : 0 < R) :
    μ {x | R < frobeniusSq (B x)} ≤
      (∫⁻ x, ENNReal.ofReal (frobeniusSq (B x)) ∂μ) / ENNReal.ofReal R := by
  have hm := ((measurable_frobeniusSq a b).comp hB).ennreal_ofReal
  refine (measure_mono (fun x hx => ENNReal.ofReal_le_ofReal (le_of_lt hx))).trans ?_
  exact meas_ge_le_lintegral_div hm.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr hR)) ENNReal.ofReal_ne_top

theorem iidMatrixLaw_gramRightInverse_tail_le {k s : ℕ} (hs : k + 2 ≤ s)
    {R : ℝ} (hR : 0 < R) :
    (iidMatrixLaw k s 1) {G | R < frobeniusSq (gramRightInverse G)} ≤
      ENNReal.ofReal ((k : ℝ) / ((s : ℝ) - k - 1)) / ENNReal.ofReal R := by
  have h := measure_frobeniusSq_tail_le (iidMatrixLaw k s 1) gramRightInverse
    (measurable_gramRightInverse k s) hR
  rwa [iidMatrixLaw_gramRightInverse_mean hs] at h

theorem iidMatrixLaw_compressed_gramRightInverse_tail_le {d k s : ℕ}
    (V : Matrix (Fin d) (Fin k) ℝ) (hV : Vᵀ * V = 1) (hs : k + 2 ≤ s)
    {R : ℝ} (hR : 0 < R) :
    (iidMatrixLaw d s 1) {U | R < frobeniusSq (gramRightInverse (Vᵀ * U))} ≤
      ENNReal.ofReal ((k : ℝ) / ((s : ℝ) - k - 1)) / ENNReal.ofReal R := by
  have h := measure_frobeniusSq_tail_le (iidMatrixLaw d s 1)
    (fun U => gramRightInverse (Vᵀ * U))
    ((measurable_gramRightInverse k s).comp
      (iidMatrixLaw_left_compression_preserving V hV 1).measurable) hR
  rwa [iidMatrixLaw_compressed_gramRightInverse_mean V hV hs] at h

end
end LowRank
