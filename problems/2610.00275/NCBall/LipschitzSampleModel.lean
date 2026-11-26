import NCBall.BallRegularity
import NCBall.NoiseMoments

/-! # The nonsmooth sample-function assumptions and their population consequences -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace NCBall

variable {E Ξ : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [MeasurableSpace Ξ]
  {μ : Measure Ξ} [IsProbabilityMeasure μ]

structure LipschitzSampleModel (μ : Measure Ξ) (f : E → ℝ) (F : Ξ → E → ℝ)
    (ℓ : Ξ → ℝ) (L : ℝ) : Prop where
  jointly_measurable : Measurable (fun p : E × Ξ => F p.2 p.1)
  sample_integrable : ∀ x, Integrable (fun ξ => F ξ x) μ
  sample_mean : ∀ x, (∫ ξ, F ξ x ∂μ) = f x
  modulus_measurable : Measurable ℓ
  modulus_nonneg : ∀ ξ, 0 ≤ ℓ ξ
  sample_lipschitz : ∀ ξ, LipschitzWith (Real.toNNReal (ℓ ξ)) (F ξ)
  modulus_square_integrable : Integrable (fun ξ => ℓ ξ ^ 2) μ
  modulus_square_moment : (∫ ξ, ℓ ξ ^ 2 ∂μ) ≤ L ^ 2

variable {f : E → ℝ} {F : Ξ → E → ℝ} {ℓ : Ξ → ℝ} {L : ℝ}

omit [IsProbabilityMeasure μ] in
theorem LipschitzSampleModel.modulus_memLp (hs : LipschitzSampleModel μ f F ℓ L) : MemLp ℓ 2 μ :=
  (memLp_two_iff_integrable_sq hs.modulus_measurable.aestronglyMeasurable).2 hs.modulus_square_integrable

theorem LipschitzSampleModel.modulus_integrable (hs : LipschitzSampleModel μ f F ℓ L) : Integrable ℓ μ :=
  hs.modulus_memLp.integrable (by norm_num)

theorem LipschitzSampleModel.modulus_mean_le (hs : LipschitzSampleModel μ f F ℓ L) (hL : 0 ≤ L) :
    (∫ ξ, ℓ ξ ∂μ) ≤ L := by
  have hv := variance_nonneg ℓ μ
  rw [variance_def' hs.modulus_memLp] at hv
  have hm := hs.modulus_square_moment
  simp only [Pi.pow_apply] at hv
  nlinarith

theorem LipschitzSampleModel.population_lipschitz (hs : LipschitzSampleModel μ f F ℓ L) (hL : 0 ≤ L) :
    LipschitzWith (Real.toNNReal L) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal L hL, dist_eq_norm, ← hs.sample_mean x, ← hs.sample_mean y,
    ← integral_sub (hs.sample_integrable x) (hs.sample_integrable y)]
  calc
    _ ≤ ∫ ξ, ‖F ξ x - F ξ y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ, ℓ ξ * dist x y ∂μ := by
      apply integral_mono_ae ((hs.sample_integrable x).sub (hs.sample_integrable y)).norm
        (hs.modulus_integrable.mul_const _)
      filter_upwards [] with ξ
      simpa only [Real.coe_toNNReal _ (hs.modulus_nonneg ξ), dist_eq_norm] using
        (hs.sample_lipschitz ξ).norm_sub_le x y
    _ = (∫ ξ, ℓ ξ ∂μ) * dist x y := integral_mul_const _ _
    _ ≤ L * dist x y := mul_le_mul_of_nonneg_right (hs.modulus_mean_le hL) dist_nonneg

end NCBall
