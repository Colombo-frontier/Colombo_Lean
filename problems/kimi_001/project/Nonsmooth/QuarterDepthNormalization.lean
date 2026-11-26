import Nonsmooth.SymmetricCoreDepth
import Nonsmooth.SymmetricBodyNormalization

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem exists_quarter_depth_normalization {K : Set E} (hconv : Convex ℝ K)
    (hcompact : IsCompact K) {r : ℝ} (hr : 0 < r)
    (hinner : Metric.closedBall (0 : E) r ⊆ K)
    (hdepth : ∀ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 →
      ENNReal.ofReal (1 / 4 : ℝ) * volume K ≤ volume (K ∩ {z | 0 ≤ ℓ z})) :
    ∃ L : E ≃L[ℝ] E,
      Metric.closedBall (0 : E) (1 / (Module.finrank ℝ E : ℝ)) ⊆ L '' K ∧
      L '' K ⊆ Metric.closedBall (0 : E) (4 * (Module.finrank ℝ E : ℝ) ^ 2) := by
  have hzero : (0 : E) ∈ K := hinner (by simpa using hr.le)
  have hK0 : volume K ≠ 0 := ne_of_gt
    ((Metric.measure_closedBall_pos volume 0 hr).trans_le (measure_mono hinner))
  have hzeroS : (0 : E) ∈ symmetricCore K := ⟨hzero, by simpa using hzero⟩
  obtain ⟨L, hLi, hLo⟩ := exists_symmetric_body_normalization (symmetricCore_convex hconv)
    (symmetricCore_compact hcompact) hzeroS (fun _ hz => symmetricCore_neg_mem hz)
    hr (symmetricCore_contains_ball hinner)
  have hsand := quarter_depth_symmetric_core_sandwich hconv hcompact hzero hK0 hdepth
  refine ⟨L, hLi.trans (image_mono hsand.1), ?_⟩
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨y, hy, heq⟩ := hsand.2 hx
  have hyL := hLo (mem_image_of_mem L hy)
  have hynorm : ‖L y‖ ≤ (Module.finrank ℝ E : ℝ) := by simpa using hyL
  rw [← heq]
  simp only [Metric.mem_closedBall, dist_zero_right]
  change ‖L ((4 * (Module.finrank ℝ E : ℝ)) • y)‖ ≤ 4 * (Module.finrank ℝ E : ℝ) ^ 2
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hynorm (by positivity : 0 ≤ 4 * (Module.finrank ℝ E : ℝ))]

end
end Nonsmooth
