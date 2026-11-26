import SampleReuse.OracleBatchProgram
import SampleReuse.OracleBatchLaw

/-! The actual two-endpoint batch error is a sum of independent centered
terms, with their almost-sure norm bounds obtained from the common-loss
assumptions. These are fixed-input batch facts, not adaptive concentration. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def batchErrorTerm {Ω E : Type*} [AddCommGroup E] [Module ℝ E] {H b : ℕ}
    (A : Ω → E) (handles : Fin b → Fin H) (i : Fin b) (tape : SampleTape H Ω) : E :=
  (b : ℝ)⁻¹ • A (tape (handles i))

theorem batchMeanTape_eq_sum {Ω E : Type*} [AddCommGroup E] [Module ℝ E] {H b : ℕ}
    (A : Ω → E) (handles : Fin b → Fin H) (tape : SampleTape H Ω) :
    batchMeanTape A handles tape = ∑ i : Fin b, batchErrorTerm A handles i tape := by
  simp only [batchMeanTape, batchErrorTerm, Finset.smul_sum]

theorem batchErrorTerm_independent {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {H b : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → E) (hA : Measurable A) (handles : Fin b → Fin H)
    (hinj : Function.Injective handles) :
    iIndepFun (batchErrorTerm A handles) (sampleTapeLaw H μ) :=
  sampleTapeLaw_sample_independent μ handles hinj _ (hA.const_smul _)

theorem batchErrorTerm_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H b : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → E) (hA : Integrable A μ)
    (handles : Fin b → Fin H) (i : Fin b) :
    Integrable (batchErrorTerm A handles i) (sampleTapeLaw H μ) :=
  (sampleTape_integrable μ A hA (handles i)).smul _

theorem batchErrorTerm_mean_zero {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H b : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → E) (hA : Integrable A μ)
    (hzero : (∫ z, A z ∂μ) = 0) (handles : Fin b → Fin H) (i : Fin b) :
    (∫ tape, batchErrorTerm A handles i tape ∂sampleTapeLaw H μ) = 0 := by
  simp only [batchErrorTerm, integral_smul, sampleTape_integral μ A hA, hzero, smul_zero]

theorem batchErrorTerm_norm_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H b : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → E) (R : ℝ)
    (hbound : ∀ᵐ z ∂μ, ‖A z‖ ≤ R) (handles : Fin b → Fin H) (i : Fin b) :
    ∀ᵐ tape ∂sampleTapeLaw H μ, ‖batchErrorTerm A handles i tape‖ ≤ R / b := by
  have hmapped : ∀ᵐ z ∂(sampleTapeLaw H μ).map (fun tape => tape (handles i)), ‖A z‖ ≤ R := by
    rw [sampleTapeLaw_marginal]
    exact hbound
  have ht : ∀ᵐ tape ∂sampleTapeLaw H μ, ‖A (tape (handles i))‖ ≤ R :=
    ae_of_ae_map (measurable_pi_apply (handles i)).aemeasurable hmapped
  filter_upwards [ht] with tape ht
  have hb : 0 ≤ (b : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    ‖batchErrorTerm A handles i tape‖ = (b : ℝ)⁻¹ * ‖A (tape (handles i))‖ := by
      simp only [batchErrorTerm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    _ ≤ (b : ℝ)⁻¹ * R := mul_le_mul_of_nonneg_left ht hb
    _ = R / b := by rw [div_eq_mul_inv, mul_comm]

theorem gradientBatchProgram_error {Ω : Type*} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (f : Point d → ℝ)
    (tape : SampleTape H Ω) (handles : Fin b → Fin H) (x y : Point d) (hb : 0 < b) :
    let P := OracleProgram.algorithm q₀ (0, 0) 0 (gradientBatchProgram handles x y)
    P.output (2 * b) (persistentRun P.toQueryPolicy F tape (2 * b)) -
      (gradient f x - gradient f y) =
        ∑ i : Fin b, batchErrorTerm
          (centeredChord (fun z => gradient (F z)) (gradient f) x y) handles i tape := by
  dsimp only
  rw [gradientBatchProgram_compiled_output]
  change batchMeanTape (fun z => gradient (F z) x - gradient (F z) y) handles tape - _ = _
  rw [batchMeanTape_centered _ _ _ _ hb, batchMeanTape_eq_sum]
  rfl

theorem hessianBatchProgram_error {Ω : Type*} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (f : Point d → ℝ)
    (tape : SampleTape H Ω) (handles : Fin b → Fin H) (x y : Point d) (hb : 0 < b) :
    let P := OracleProgram.algorithm q₀ (0, 0) 0 (hessianBatchProgram handles x y)
    P.output (2 * b) (persistentRun P.toQueryPolicy F tape (2 * b)) -
      (hessian f x - hessian f y) =
        ∑ i : Fin b, batchErrorTerm
          (centeredChord (fun z => hessian (F z)) (hessian f) x y) handles i tape := by
  dsimp only
  rw [hessianBatchProgram_compiled_output]
  change batchMeanTape (fun z => hessian (F z) x - hessian (F z) y) handles tape - _ = _
  rw [batchMeanTape_centered _ _ _ _ hb, batchMeanTape_eq_sum]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {H d b : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}

theorem Admissible.gradient_batch_terms_centered (h : Admissible μ P f F x₀)
    (x y : Point d) (handles : Fin b → Fin H) (i : Fin b) :
    (∫ tape, batchErrorTerm
      (centeredChord (fun z => gradient (F z)) (gradient f) x y) handles i tape
        ∂sampleTapeLaw H μ) = 0 :=
  batchErrorTerm_mean_zero μ _
    (centeredChord_integrable _ _ x y (h.gradient_integrable x) (h.gradient_integrable y))
    (h.gradient_chord_unbiased x y) handles i

theorem Admissible.hessian_batch_terms_centered (h : Admissible μ P f F x₀)
    (x y : Point d) (handles : Fin b → Fin H) (i : Fin b) :
    (∫ tape, batchErrorTerm
      (centeredChord (fun z => hessian (F z)) (hessian f) x y) handles i tape
        ∂sampleTapeLaw H μ) = 0 :=
  batchErrorTerm_mean_zero μ _
    (centeredChord_integrable _ _ x y (h.hessian_integrable x) (h.hessian_integrable y))
    (h.hessian_chord_unbiased x y) handles i

theorem Admissible.gradient_batch_terms_bounded (h : Admissible μ P f F x₀)
    (x y : Point d) (handles : Fin b → Fin H) (i : Fin b) :
    ∀ᵐ tape ∂sampleTapeLaw H μ,
      ‖batchErrorTerm (centeredChord (fun z => gradient (F z)) (gradient f) x y)
        handles i tape‖ ≤ 2 * min P.gradientNoise (P.gradientLip * ‖x-y‖) / b :=
  batchErrorTerm_norm_le μ _ _ (h.gradient_chord_bound.mono (fun _ hz => hz x y)) handles i

theorem Admissible.hessian_batch_terms_bounded (h : Admissible μ P f F x₀)
    (x y : Point d) (handles : Fin b → Fin H) (i : Fin b) :
    ∀ᵐ tape ∂sampleTapeLaw H μ,
      ‖batchErrorTerm (centeredChord (fun z => hessian (F z)) (hessian f) x y)
        handles i tape‖ ≤ 2 * min P.hessianNoise (P.hessianLip * ‖x-y‖) / b :=
  batchErrorTerm_norm_le μ _ _ (h.hessian_chord_bound.mono (fun _ hz => hz x y)) handles i

end
end SampleReuse
