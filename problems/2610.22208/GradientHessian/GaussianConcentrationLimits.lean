import GradientHessian.GaussianConcentrationHessian

/-! Continuity and both endpoint limits of the actual Gaussian semigroup.
The uniform bound is on the input function, not an assumed semigroup limit. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter
open scoped Topology NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem mehler_norm_le {f : E → ℝ} {D : ℝ} (hD : ∀ z, ‖f z‖ ≤ D)
    (ρ : ℝ) (x : E) : ‖mehler E ρ f x‖ ≤ D := by
  simpa only [measureReal_univ_eq_one, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := euclideanGaussianLaw E)
      (ae_of_all _ fun z => hD (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)))

theorem mehler_joint_continuous {f : E → ℝ} (hf : Continuous f) {D : ℝ}
    (hD : ∀ z, ‖f z‖ ≤ D) :
    Continuous (fun p : ℝ × E => mehler E p.1 f p.2) := by
  apply continuous_of_dominated (bound := fun _ => D)
  · intro p
    exact (hf.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  · intro p
    exact ae_of_all _ fun z => hD _
  · exact integrable_const _
  · apply ae_of_all
    intro z
    exact hf.comp ((continuous_fst.smul continuous_snd).add
      ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_fst.pow 2))).smul continuous_const))

omit [BorelSpace E] in
@[simp] theorem mehler_zero (f : E → ℝ) (x : E) :
    mehler E 0 f x = ∫ z, f z ∂euclideanGaussianLaw E := by
  simp [mehler]

@[simp] theorem mehler_one (f : E → ℝ) (x : E) : mehler E 1 f x = f x := by
  simp [mehler]

theorem ou_tendsto_mean {f : E → ℝ} (hf : Continuous f) {D : ℝ}
    (hD : ∀ z, ‖f z‖ ≤ D) (x : E) :
    Tendsto (fun t => ornsteinUhlenbeck E t f x) atTop
      (𝓝 (∫ z, f z ∂euclideanGaussianLaw E)) := by
  have hc : Continuous (fun ρ : ℝ => mehler E ρ f x) :=
    (mehler_joint_continuous E hf hD).comp (continuous_id.prodMk continuous_const)
  simpa only [mehler_zero] using hc.continuousAt.tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero

def mehlerSquareMean (ρ : ℝ) (f : E → ℝ) : ℝ :=
  ∫ x, (mehler E ρ f x) ^ 2 ∂euclideanGaussianLaw E

theorem mehlerSquareMean_continuous {f : E → ℝ} (hf : Continuous f) {D : ℝ}
    (hD : ∀ z, ‖f z‖ ≤ D) : Continuous (fun ρ => mehlerSquareMean E ρ f) := by
  apply continuous_of_dominated (bound := fun _ => D ^ 2)
  · intro ρ
    exact (((mehler_joint_continuous E hf hD).comp
      (continuous_const.prodMk continuous_id)).pow 2).aestronglyMeasurable
  · intro ρ
    apply ae_of_all
    intro x
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (mehler_norm_le E hD ρ x) 2
  · exact integrable_const _
  · apply ae_of_all
    intro x
    exact ((mehler_joint_continuous E hf hD).comp
      (continuous_id.prodMk continuous_const)).pow 2

theorem ou_squareMean_continuous {f : E → ℝ} (hf : Continuous f) {D : ℝ}
    (hD : ∀ z, ‖f z‖ ≤ D) :
    Continuous (fun t => ∫ x, (ornsteinUhlenbeck E t f x) ^ 2 ∂euclideanGaussianLaw E) :=
  (mehlerSquareMean_continuous E hf hD).comp (Real.continuous_exp.comp continuous_neg)

theorem ou_squareMean_tendsto {f : E → ℝ} (hf : Continuous f) {D : ℝ}
    (hD : ∀ z, ‖f z‖ ≤ D) :
    Tendsto (fun t => ∫ x, (ornsteinUhlenbeck E t f x) ^ 2 ∂euclideanGaussianLaw E)
      atTop (𝓝 ((∫ z, f z ∂euclideanGaussianLaw E) ^ 2)) := by
  have h := (mehlerSquareMean_continuous E hf hD).continuousAt.tendsto.comp
    Real.tendsto_exp_neg_atTop_nhds_zero
  simpa only [mehlerSquareMean, mehler_zero, integral_const,
    measureReal_univ_eq_one, smul_eq_mul, one_mul] using h

end GradientHessian.GaussianConcentration
