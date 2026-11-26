import SampleReuse.OracleRootBatch
import SampleReuse.VectorConcentration

/-! Vector-norm confidence for the actual compiled gradient root and chord
batches, with logarithmic dimension dependence. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {H d b : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}

theorem Admissible.gradient_centered_chord_measurable (h : Admissible μ P f F x₀)
    (x y : Point d) :
    Measurable (centeredChord (fun z => gradient (F z)) (gradient f) x y) := by
  exact ((h.gradient_measurable.comp (measurable_id.prodMk measurable_const)).sub
    (h.gradient_measurable.comp (measurable_id.prodMk measurable_const))).sub measurable_const

theorem Admissible.gradient_batch_confidence (h : Admissible μ P f F x₀)
    (x y : Point d) (handles : Fin b → Fin H) (hinj : Function.Injective handles)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hb : 0 < b)
    (hsize : 32 * (matrixMomentOrder (d + 1) δ : ℝ) *
      (2 * min P.gradientNoise (P.gradientLip * ‖x-y‖))^2 ≤ (b : ℝ) * η^2) :
    (sampleTapeLaw H μ).real {tape |
      η ≤ ‖batchMeanTape (gradientChordSample F (x, y)) handles tape -
        (gradient f x - gradient f y)‖} ≤ δ := by
  let A := centeredChord (fun z => gradient (F z)) (gradient f) x y
  let σ := 2 * min P.gradientNoise (P.gradientLip * ‖x-y‖)
  have hA : Measurable A := h.gradient_centered_chord_measurable x y
  have hAi : Integrable A μ := centeredChord_integrable _ _ x y
    (h.gradient_integrable x) (h.gradient_integrable y)
  have hσ : 0 ≤ σ := mul_nonneg (by norm_num)
    (le_min P.gradientNoise_pos.le (mul_nonneg P.gradientLip_pos.le (norm_nonneg _)))
  have hX : ∀ i : Fin b, Measurable (fun tape : SampleTape H Ω => A (tape (handles i))) :=
    fun i => hA.comp (measurable_pi_apply (handles i))
  have hbound : ∀ i : Fin b, ∀ᵐ tape ∂sampleTapeLaw H μ, ‖A (tape (handles i))‖ ≤ σ := by
    intro i
    have hmapped : ∀ᵐ z ∂(sampleTapeLaw H μ).map (fun tape => tape (handles i)), ‖A z‖ ≤ σ := by
      rw [sampleTapeLaw_marginal]
      exact h.gradient_chord_bound.mono (fun _ hz => hz x y)
    exact ae_of_ae_map (measurable_pi_apply (handles i)).aemeasurable hmapped
  have hzero : ∀ i : Fin b,
      (∫ tape : SampleTape H Ω, A (tape (handles i)) ∂sampleTapeLaw H μ) = 0 := by
    intro i
    rw [sampleTape_integral μ A hAi (handles i)]
    exact h.gradient_chord_unbiased x y
  have hsize' : 32 * (matrixMomentOrder (Module.finrank ℝ (Point d) + 1) δ : ℝ) * σ^2 ≤
      (b : ℝ) * η^2 := by simpa only [Point, finrank_euclideanSpace_fin] using hsize
  have hc := independent_vector_average_confidence
    (fun i (tape : SampleTape H Ω) => A (tape (handles i))) hX hσ hη hδ hb hbound
    (sampleTapeLaw_sample_independent μ handles hinj A hA) hzero hsize'
  have he (tape : SampleTape H Ω) :
      batchMeanTape (gradientChordSample F (x, y)) handles tape - (gradient f x - gradient f y) =
        batchMeanTape A handles tape := batchMeanTape_centered _ _ _ _ hb
  simp_rw [he]
  exact hc

theorem Admissible.gradientBatchProgram_confidence (h : Admissible μ P f F x₀)
    (q₀ : PersistentQuery H d) (x y : Point d) (handles : Fin b → Fin H)
    (hinj : Function.Injective handles) {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hb : 0 < b)
    (hsize : 32 * (matrixMomentOrder (d + 1) δ : ℝ) *
      (2 * min P.gradientNoise (P.gradientLip * ‖x-y‖))^2 ≤ (b : ℝ) * η^2) :
    let alg := OracleProgram.algorithm q₀ (0, 0) 0 (gradientBatchProgram handles x y)
    (sampleTapeLaw H μ).real {tape |
      η ≤ ‖alg.output (2 * b) (persistentRun alg.toQueryPolicy F tape (2 * b)) -
        (gradient f x - gradient f y)‖} ≤ δ := by
  dsimp only
  simp_rw [gradientBatchProgram_compiled_output]
  exact h.gradient_batch_confidence x y handles hinj hη hδ hb hsize

theorem Admissible.gradient_root_confidence (h : Admissible μ P f F x₀)
    (x : Point d) (handles : Fin b → Fin H) (hinj : Function.Injective handles)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hb : 0 < b)
    (hsize : 32 * (matrixMomentOrder (d + 1) δ : ℝ) * P.gradientNoise^2 ≤ (b : ℝ) * η^2) :
    (sampleTapeLaw H μ).real {tape |
      η ≤ ‖batchMeanTape (fun z => gradient (F z) x) handles tape - gradient f x‖} ≤ δ := by
  let A := fun z => gradient (F z) x - gradient f x
  have hA : Measurable A :=
    (h.gradient_measurable.comp (measurable_id.prodMk measurable_const)).sub measurable_const
  have hAi : Integrable A μ := (h.gradient_integrable x).sub (integrable_const _)
  have hX : ∀ i : Fin b, Measurable (fun tape : SampleTape H Ω => A (tape (handles i))) :=
    fun i => hA.comp (measurable_pi_apply (handles i))
  have hbound : ∀ i : Fin b, ∀ᵐ tape ∂sampleTapeLaw H μ,
      ‖A (tape (handles i))‖ ≤ P.gradientNoise := by
    intro i
    have hmapped : ∀ᵐ z ∂(sampleTapeLaw H μ).map (fun tape => tape (handles i)),
        ‖A z‖ ≤ P.gradientNoise := by
      rw [sampleTapeLaw_marginal]
      exact h.noise_bound.mono (fun _ hz => (hz x).1)
    exact ae_of_ae_map (measurable_pi_apply (handles i)).aemeasurable hmapped
  have hzero : ∀ i : Fin b,
      (∫ tape : SampleTape H Ω, A (tape (handles i)) ∂sampleTapeLaw H μ) = 0 := by
    intro i
    rw [sampleTape_integral μ A hAi (handles i)]
    simp [A, integral_sub (h.gradient_integrable x) (integrable_const (gradient f x)),
      h.gradient_unbiased x]
  have hsize' : 32 * (matrixMomentOrder (Module.finrank ℝ (Point d) + 1) δ : ℝ) *
      P.gradientNoise^2 ≤ (b : ℝ) * η^2 := by
    simpa only [Point, finrank_euclideanSpace_fin] using hsize
  have hc := independent_vector_average_confidence
    (fun i (tape : SampleTape H Ω) => A (tape (handles i))) hX P.gradientNoise_pos.le
    hη hδ hb hbound (sampleTapeLaw_sample_independent μ handles hinj A hA) hzero hsize'
  have he (tape : SampleTape H Ω) :
      batchMeanTape (fun z => gradient (F z) x) handles tape - gradient f x =
        batchMeanTape A handles tape := batchMeanTape_centered _ _ _ _ hb
  simp_rw [he]
  exact hc

theorem Admissible.gradientRootProgram_confidence (h : Admissible μ P f F x₀)
    (q₀ : PersistentQuery H d) (x : Point d) (handles : Fin b → Fin H)
    (hinj : Function.Injective handles) {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hb : 0 < b)
    (hsize : 32 * (matrixMomentOrder (d + 1) δ : ℝ) * P.gradientNoise^2 ≤ (b : ℝ) * η^2) :
    let alg := OracleProgram.algorithm q₀ (0, 0) 0 (gradientRootProgram handles x)
    (sampleTapeLaw H μ).real {tape |
      η ≤ ‖alg.output b (persistentRun alg.toQueryPolicy F tape b) - gradient f x‖} ≤ δ := by
  dsimp only
  simp_rw [gradientRootProgram_compiled_output]
  exact h.gradient_root_confidence x handles hinj hη hδ hb hsize

end
end SampleReuse
