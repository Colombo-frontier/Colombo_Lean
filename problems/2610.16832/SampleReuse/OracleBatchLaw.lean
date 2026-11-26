import SampleReuse.OraclePersistent
import SampleReuse.ChordError
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Probability laws of batches read from an immutable iid tape. Distinct
fixed handles give actual independent samples. Endpoint choices in this file
are fixed; conditional freshness for adaptive histories is not asserted. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

theorem sampleTapeLaw_selection {Ω : Type*} [MeasurableSpace Ω] {H b : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (handles : Fin b → Fin H)
    (hinj : Function.Injective handles) :
    (sampleTapeLaw H μ).map (fun tape i => tape (handles i)) = sampleTapeLaw b μ := by
  have hi := iIndepFun.precomp hinj (sampleTapeLaw_independent H μ)
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (handles i)).aemeasurable)] at hi
  change (sampleTapeLaw H μ).map (fun tape i => tape (handles i)) =
    Measure.pi (fun i : Fin b => (sampleTapeLaw H μ).map (fun tape => tape (handles i))) at hi
  simpa only [sampleTapeLaw_marginal] using hi

theorem sampleTapeLaw_sample_independent {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] {H b : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (handles : Fin b → Fin H)
    (hinj : Function.Injective handles) (A : Ω → E) (hA : Measurable A) :
    iIndepFun (fun i (tape : SampleTape H Ω) => A (tape (handles i)))
      (sampleTapeLaw H μ) :=
  (iIndepFun.precomp hinj (sampleTapeLaw_independent H μ)).comp (fun _ => A) (fun _ => hA)

def batchMeanTape {Ω E : Type*} [AddCommGroup E] [Module ℝ E] {H b : ℕ}
    (A : Ω → E) (handles : Fin b → Fin H) (tape : SampleTape H Ω) : E :=
  (b : ℝ)⁻¹ • ∑ i : Fin b, A (tape (handles i))

theorem batchMeanTape_measurable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {H b : ℕ} (A : Ω → E) (hA : Measurable A) (handles : Fin b → Fin H) :
    Measurable (batchMeanTape A handles) := by
  unfold batchMeanTape
  exact (Finset.measurable_sum _ (fun i _ => hA.comp (measurable_pi_apply (handles i)))).const_smul _

theorem batchMeanTape_law {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {H b : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → E) (hA : Measurable A) (handles : Fin b → Fin H)
    (hinj : Function.Injective handles) :
    (sampleTapeLaw H μ).map (batchMeanTape A handles) =
      (sampleTapeLaw b μ).map (batchMeanTape A id) := by
  have hm : Measurable (fun tape : SampleTape H Ω => fun i => tape (handles i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (handles i))
  calc
    _ = ((sampleTapeLaw H μ).map (fun tape i => tape (handles i))).map
        (batchMeanTape A id) :=
      (Measure.map_map (batchMeanTape_measurable A hA id) hm).symm
    _ = _ := by rw [sampleTapeLaw_selection μ handles hinj]

theorem sampleTape_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {H : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → E) (hA : Integrable A μ) (r : Fin H) :
    Integrable (fun tape : SampleTape H Ω => A (tape r)) (sampleTapeLaw H μ) := by
  have hp : MeasurePreserving (fun tape : SampleTape H Ω => tape r) (sampleTapeLaw H μ) μ :=
    ⟨measurable_pi_apply r, sampleTapeLaw_marginal H μ r⟩
  exact (hp.integrable_comp hA.aestronglyMeasurable).mpr hA

theorem sampleTape_integral {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → E) (hA : Integrable A μ) (r : Fin H) :
    (∫ tape : SampleTape H Ω, A (tape r) ∂sampleTapeLaw H μ) = ∫ z, A z ∂μ := by
  have hm : AEStronglyMeasurable A ((sampleTapeLaw H μ).map (fun tape => tape r)) := by
    simpa only [sampleTapeLaw_marginal] using hA.aestronglyMeasurable
  rw [← integral_map (measurable_pi_apply r).aemeasurable hm, sampleTapeLaw_marginal]

theorem batchMeanTape_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H b : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → E) (hA : Integrable A μ)
    (handles : Fin b → Fin H) :
    Integrable (batchMeanTape A handles) (sampleTapeLaw H μ) := by
  exact (integrable_finset_sum _ (fun i _ => sampleTape_integrable μ A hA (handles i))).smul _

theorem batchMeanTape_integral {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H b : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → E) (hA : Integrable A μ) (handles : Fin b → Fin H) (hb : 0 < b) :
    (∫ tape, batchMeanTape A handles tape ∂sampleTapeLaw H μ) = ∫ z, A z ∂μ := by
  simp only [batchMeanTape, integral_smul]
  rw [integral_finset_sum _ (fun i _ => sampleTape_integrable μ A hA (handles i))]
  simp_rw [sampleTape_integral μ A hA]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hb.ne')]
  exact one_smul _ _

theorem batchMeanTape_centered {Ω E : Type*} [AddCommGroup E] [Module ℝ E]
    {H b : ℕ} (A : Ω → E) (a : E) (handles : Fin b → Fin H)
    (tape : SampleTape H Ω) (hb : 0 < b) :
    batchMeanTape A handles tape - a = batchMeanTape (fun z => A z - a) handles tape := by
  simp only [batchMeanTape, Finset.sum_sub_distrib, smul_sub]
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hb.ne')]
  exact (one_smul _ _).symm

theorem batchMeanTape_error_law {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {H b : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → E) (hA : Measurable A) (a : E) (handles : Fin b → Fin H)
    (hinj : Function.Injective handles) (hb : 0 < b) :
    (sampleTapeLaw H μ).map (fun tape => batchMeanTape A handles tape - a) =
      (sampleTapeLaw b μ).map (batchMeanTape (fun z => A z - a) id) := by
  rw [show (fun tape => batchMeanTape A handles tape - a) =
    batchMeanTape (fun z => A z - a) handles from
      funext (fun tape => batchMeanTape_centered A a handles tape hb)]
  exact batchMeanTape_law μ _ (hA.sub measurable_const) handles hinj

theorem Admissible.gradient_batch_unbiased {Ω : Type*} [MeasurableSpace Ω]
    {d H b : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (x y : Point d)
    (handles : Fin b → Fin H) (hb : 0 < b) :
    (∫ tape, batchMeanTape (fun z => gradient (F z) x - gradient (F z) y)
      handles tape ∂sampleTapeLaw H μ) = gradient f x - gradient f y := by
  calc
    _ = ∫ z, (gradient (F z) x - gradient (F z) y) ∂μ :=
      batchMeanTape_integral μ _ ((h.gradient_integrable x).sub (h.gradient_integrable y)) handles hb
    _ = _ := by rw [integral_sub (h.gradient_integrable x) (h.gradient_integrable y),
      h.gradient_unbiased x, h.gradient_unbiased y]

theorem Admissible.hessian_batch_unbiased {Ω : Type*} [MeasurableSpace Ω]
    {d H b : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) (x y : Point d)
    (handles : Fin b → Fin H) (hb : 0 < b) :
    (∫ tape, batchMeanTape (fun z => hessian (F z) x - hessian (F z) y)
      handles tape ∂sampleTapeLaw H μ) = hessian f x - hessian f y := by
  calc
    _ = ∫ z, (hessian (F z) x - hessian (F z) y) ∂μ :=
      batchMeanTape_integral μ _ ((h.hessian_integrable x).sub (h.hessian_integrable y)) handles hb
    _ = _ := by rw [integral_sub (h.hessian_integrable x) (h.hessian_integrable y),
      h.hessian_unbiased x, h.hessian_unbiased y]

end
end SampleReuse
