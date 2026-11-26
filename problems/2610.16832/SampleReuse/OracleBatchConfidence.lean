import SampleReuse.OracleBatchError
import SampleReuse.OperatorConfidence
import SecondOrder.HessianSymmetry

/-! Operator-norm confidence for the actual persistent Hessian batch. All
probabilistic premises are derived from the immutable iid tape and the scalar
loss assumptions. The endpoints and selected distinct handles are fixed. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {H d b : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}

theorem Admissible.hessian_centered_chord_measurable (h : Admissible μ P f F x₀)
    (x y : Point d) :
    Measurable (centeredChord (fun z => hessian (F z)) (hessian f) x y) := by
  exact ((h.hessian_measurable.comp (measurable_id.prodMk measurable_const)).sub
    (h.hessian_measurable.comp (measurable_id.prodMk measurable_const))).sub measurable_const

theorem Admissible.hessian_centered_chord_symmetric (h : Admissible μ P f F x₀)
    (x y : Point d) :
    ∀ᵐ z ∂μ, (centeredChord (fun z => hessian (F z)) (hessian f) x y z).toLinearMap.IsSymmetric := by
  filter_upwards [h.sample_regularity] with z hz
  exact ((hessian_isSymmetric hz.1 x).sub (hessian_isSymmetric hz.1 y)).sub
    ((hessian_isSymmetric h.population_smooth x).sub (hessian_isSymmetric h.population_smooth y))

theorem Admissible.hessian_batch_confidence (h : Admissible μ P f F x₀)
    (x y : Point d) (handles : Fin b → Fin H) (hinj : Function.Injective handles)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hb : 0 < b)
    (hsize : 8 * (matrixMomentOrder (d + 1) δ : ℝ) *
      (2 * min P.hessianNoise (P.hessianLip * ‖x-y‖))^2 ≤ (b : ℝ) * η^2) :
    (sampleTapeLaw H μ).real {tape |
      η ≤ ‖batchMeanTape (hessianChordSample F (x, y)) handles tape -
        (hessian f x - hessian f y)‖} ≤ δ := by
  let A := centeredChord (fun z => hessian (F z)) (hessian f) x y
  let σ := 2 * min P.hessianNoise (P.hessianLip * ‖x-y‖)
  have hA : Measurable A := h.hessian_centered_chord_measurable x y
  have hAi : Integrable A μ := centeredChord_integrable _ _ x y
    (h.hessian_integrable x) (h.hessian_integrable y)
  have hσ : 0 ≤ σ := mul_nonneg (by norm_num)
    (le_min P.hessianNoise_pos.le (mul_nonneg P.hessianLip_pos.le (norm_nonneg _)))
  have hX : ∀ i : Fin b, Measurable (fun tape : SampleTape H Ω => A (tape (handles i))) :=
    fun i => hA.comp (measurable_pi_apply (handles i))
  have hbound : ∀ i : Fin b, ∀ᵐ tape ∂sampleTapeLaw H μ, ‖A (tape (handles i))‖ ≤ σ := by
    intro i
    have hmapped : ∀ᵐ z ∂(sampleTapeLaw H μ).map (fun tape => tape (handles i)), ‖A z‖ ≤ σ := by
      rw [sampleTapeLaw_marginal]
      exact h.hessian_chord_bound.mono (fun _ hz => hz x y)
    exact ae_of_ae_map (measurable_pi_apply (handles i)).aemeasurable hmapped
  have hzero : ∀ i : Fin b,
      (∫ tape : SampleTape H Ω, A (tape (handles i)) ∂sampleTapeLaw H μ) = 0 := by
    intro i
    rw [sampleTape_integral μ A hAi (handles i)]
    exact h.hessian_chord_unbiased x y
  have hsym : ∀ i : Fin b, ∀ᵐ tape ∂sampleTapeLaw H μ,
      (A (tape (handles i))).toLinearMap.IsSymmetric := by
    intro i
    have hmapped : ∀ᵐ z ∂(sampleTapeLaw H μ).map (fun tape => tape (handles i)),
        (A z).toLinearMap.IsSymmetric := by
      rw [sampleTapeLaw_marginal]
      exact h.hessian_centered_chord_symmetric x y
    exact ae_of_ae_map (measurable_pi_apply (handles i)).aemeasurable hmapped
  have hsize' : 8 * (matrixMomentOrder (Module.finrank ℝ (Point d) + 1) δ : ℝ) * σ^2 ≤
      (b : ℝ) * η^2 := by simpa only [Point, finrank_euclideanSpace_fin] using hsize
  have hc := independent_operator_average_confidence
    (fun i (tape : SampleTape H Ω) => A (tape (handles i))) hX hσ hη hδ hb hbound
    (sampleTapeLaw_sample_independent μ handles hinj A hA) hzero hsym hsize'
  have he (tape : SampleTape H Ω) :
      batchMeanTape (hessianChordSample F (x, y)) handles tape - (hessian f x - hessian f y) =
        batchMeanTape A handles tape :=
    batchMeanTape_centered _ _ _ _ hb
  simp_rw [he]
  exact hc

/-- Confidence for the numerical output of the compiled two-calls-per-sample
program itself, rather than an abstract estimator with assumed accuracy. -/
theorem Admissible.hessianBatchProgram_confidence (h : Admissible μ P f F x₀)
    (q₀ : PersistentQuery H d) (x y : Point d) (handles : Fin b → Fin H)
    (hinj : Function.Injective handles) {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hb : 0 < b)
    (hsize : 8 * (matrixMomentOrder (d + 1) δ : ℝ) *
      (2 * min P.hessianNoise (P.hessianLip * ‖x-y‖))^2 ≤ (b : ℝ) * η^2) :
    let alg := OracleProgram.algorithm q₀ (0, 0) 0 (hessianBatchProgram handles x y)
    (sampleTapeLaw H μ).real {tape |
      η ≤ ‖alg.output (2 * b) (persistentRun alg.toQueryPolicy F tape (2 * b)) -
        (hessian f x - hessian f y)‖} ≤ δ := by
  dsimp only
  simp_rw [hessianBatchProgram_compiled_output]
  exact h.hessian_batch_confidence x y handles hinj hη hδ hb hsize

end
end SampleReuse
