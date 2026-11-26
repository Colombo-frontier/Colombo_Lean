import HeavyTail.AdaptiveKernelExecution
import HeavyTail.GaussianAdaptiveSampler
import HeavyTail.GaussianAdaptiveChange
import HeavyTail.GaussianTesting

/-! Actual finite-horizon adaptive Gaussian transcript laws. The likelihood
ratio is defined recursively from observed replies, and the change of measure
and second-moment bound follow by induction over fresh oracle calls. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace HeavyTail.GaussianLower
noncomputable section
universe u

variable {E Seed : Type u} {X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace Seed] [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ}

def gaussianResponseKernel (mean : X → E) (hm : Measurable mean) (σ : ℝ) : Kernel X E :=
  kernelOfSampler (GaussianEstimates.euclideanGaussianLaw E)
    (fun ω : X × E ↦ mean ω.1 + σ • ω.2) (by fun_prop)

instance gaussianResponseKernel_markov (mean : X → E) (hm : Measurable mean) (σ : ℝ) :
    IsMarkovKernel (gaussianResponseKernel mean hm σ) := by
  unfold gaussianResponseKernel
  infer_instance

def gaussianStateStep (A : AdaptiveKernel.Policy Seed X E Y T) (mean : X → E)
    (σ : ℝ) (n : ℕ) (ω : AdaptiveKernel.History Seed E n × E) :
    AdaptiveKernel.History Seed E (n + 1) :=
  (ω.1, mean (A.query n ω.1) + σ • ω.2)

lemma gaussianStateStep_measurable (A : AdaptiveKernel.Policy Seed X E Y T)
    {mean : X → E} (hm : Measurable mean) (σ : ℝ) (n : ℕ) :
    Measurable (gaussianStateStep A mean σ n) := by
  change Measurable (fun ω : AdaptiveKernel.History Seed E n × E ↦
    (ω.1, mean (A.query n ω.1) + σ • ω.2))
  have hq := A.query_measurable n
  fun_prop

theorem gaussian_historyLaw_succ (A : AdaptiveKernel.Policy Seed X E Y T)
    (P : Measure Seed) [IsProbabilityMeasure P] {mean : X → E} (hm : Measurable mean)
    (σ : ℝ) (n : ℕ) :
    A.historyLaw P (gaussianResponseKernel mean hm σ) (n + 1) =
      ((A.historyLaw P (gaussianResponseKernel mean hm σ) n).prod
        (GaussianEstimates.euclideanGaussianLaw E)).map (gaussianStateStep A mean σ n) := by
  rw [AdaptiveKernel.Policy.historyLaw_succ]
  unfold AdaptiveKernel.Policy.replyKernel gaussianResponseKernel
  rw [kernelOfSampler_comap, compProd_kernelOfSampler]
  rfl

def gaussianMeanGap (A : AdaptiveKernel.Policy Seed X E Y T) (m₀ m₁ : X → E)
    (σ : ℝ) (n : ℕ) (h : AdaptiveKernel.History Seed E n) : E :=
  σ⁻¹ • (m₁ (A.query n h) - m₀ (A.query n h))

lemma gaussianMeanGap_measurable (A : AdaptiveKernel.Policy Seed X E Y T)
    {m₀ m₁ : X → E} (h₀ : Measurable m₀) (h₁ : Measurable m₁) (σ : ℝ) (n : ℕ) :
    Measurable (gaussianMeanGap A m₀ m₁ σ n) := by
  unfold gaussianMeanGap
  have hq := A.query_measurable n
  fun_prop

def gaussianPathLikelihood (A : AdaptiveKernel.Policy Seed X E Y T) (m₀ m₁ : X → E)
    (σ : ℝ) : (n : ℕ) → AdaptiveKernel.History Seed E n → ℝ
  | 0 => fun _ ↦ 1
  | n + 1 => fun h ↦ gaussianPathLikelihood A m₀ m₁ σ n h.1 *
      exponentialRatio (gaussianMeanGap A m₀ m₁ σ n h.1)
        (σ⁻¹ • (h.2 - m₀ (A.query n h.1)))

omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma gaussianPathLikelihood_nonneg (A : AdaptiveKernel.Policy Seed X E Y T)
    (m₀ m₁ : X → E) (σ : ℝ) (n : ℕ) :
    ∀ h, 0 ≤ gaussianPathLikelihood A m₀ m₁ σ n h := by
  induction n with
  | zero => exact fun _ ↦ zero_le_one
  | succ n ih => exact fun h ↦ mul_nonneg (ih h.1) (Real.exp_pos _).le

lemma gaussianPathLikelihood_measurable (A : AdaptiveKernel.Policy Seed X E Y T)
    {m₀ m₁ : X → E} (h₀ : Measurable m₀) (h₁ : Measurable m₁) (σ : ℝ) (n : ℕ) :
    Measurable (gaussianPathLikelihood A m₀ m₁ σ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun h : AdaptiveKernel.History Seed E n × E ↦
      gaussianPathLikelihood A m₀ m₁ σ n h.1 *
        Real.exp (⟪gaussianMeanGap A m₀ m₁ σ n h.1,
          σ⁻¹ • (h.2 - m₀ (A.query n h.1))⟫_ℝ -
            ‖gaussianMeanGap A m₀ m₁ σ n h.1‖ ^ 2 / 2))
    have hg := gaussianMeanGap_measurable A h₀ h₁ σ n
    have hq := A.query_measurable n
    fun_prop

omit [BorelSpace E] [FiniteDimensional ℝ E] in
theorem gaussianPathLikelihood_step (A : AdaptiveKernel.Policy Seed X E Y T)
    (m₀ m₁ : X → E) {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ)
    (ω : AdaptiveKernel.History Seed E n × E) :
    gaussianPathLikelihood A m₀ m₁ σ (n + 1) (gaussianStateStep A m₀ σ n ω) =
      likelihoodStep (gaussianPathLikelihood A m₀ m₁ σ n) (gaussianMeanGap A m₀ m₁ σ n) ω := by
  simp only [gaussianPathLikelihood, gaussianStateStep, likelihoodStep,
    add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hσ, one_smul]

omit [BorelSpace E] [FiniteDimensional ℝ E] in
theorem gaussianStateStep_shift (A : AdaptiveKernel.Policy Seed X E Y T)
    (m₀ m₁ : X → E) {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    gaussianStateStep A m₁ σ n = gaussianStateStep A m₀ σ n ∘
      conditionalGaussianShift (gaussianMeanGap A m₀ m₁ σ n) := by
  funext ω
  simp only [gaussianStateStep, Function.comp_apply, conditionalGaussianShift,
    gaussianMeanGap, smul_add, smul_smul, mul_inv_cancel₀ hσ, one_smul]
  congr 1
  abel

/-- Exact likelihood identity for every prefix of the actual adaptive execution. -/
theorem gaussian_historyLaw_likelihood (A : AdaptiveKernel.Policy Seed X E Y T)
    (P : Measure Seed) [IsProbabilityMeasure P] {m₀ m₁ : X → E}
    (h₀ : Measurable m₀) (h₁ : Measurable m₁) {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    A.historyLaw P (gaussianResponseKernel m₁ h₁ σ) n =
      (A.historyLaw P (gaussianResponseKernel m₀ h₀ σ) n).withDensity
        (fun h ↦ ENNReal.ofReal (gaussianPathLikelihood A m₀ m₁ σ n h)) := by
  induction n with
  | zero => simp [AdaptiveKernel.Policy.historyLaw_zero, gaussianPathLikelihood]
  | succ n ih =>
    rw [gaussian_historyLaw_succ A P h₀ σ n, gaussian_historyLaw_succ A P h₁ σ n]
    exact gaussian_transition_change_of_measure _ _
      (gaussianPathLikelihood_measurable A h₀ h₁ σ n)
      (gaussianMeanGap_measurable A h₀ h₁ σ n)
      (gaussianPathLikelihood_nonneg A m₀ m₁ σ n) ih
      (gaussianStateStep_measurable A h₀ σ n)
      (gaussianPathLikelihood_measurable A h₀ h₁ σ (n + 1))
      (gaussianStateStep_shift A m₀ m₁ hσ n) (gaussianPathLikelihood_step A m₀ m₁ hσ n)

theorem gaussianPathLikelihood_integrable (A : AdaptiveKernel.Policy Seed X E Y T)
    (P : Measure Seed) [IsProbabilityMeasure P] {m₀ m₁ : X → E}
    (h₀ : Measurable m₀) (h₁ : Measurable m₁) {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    Integrable (gaussianPathLikelihood A m₀ m₁ σ n)
      (A.historyLaw P (gaussianResponseKernel m₀ h₀ σ) n) := by
  induction n with
  | zero => exact integrable_const 1
  | succ n ih =>
    rw [gaussian_historyLaw_succ A P h₀ σ n]
    apply (integrable_map_measure
      (gaussianPathLikelihood_measurable A h₀ h₁ σ (n + 1)).aestronglyMeasurable
      (gaussianStateStep_measurable A h₀ σ n).aemeasurable).mpr
    simpa only [Function.comp_def, gaussianPathLikelihood_step A m₀ m₁ hσ n] using
      likelihoodStep_integrable (gaussianPathLikelihood_measurable A h₀ h₁ σ n)
        (gaussianMeanGap_measurable A h₀ h₁ σ n) ih

theorem gaussianPathLikelihood_mean (A : AdaptiveKernel.Policy Seed X E Y T)
    (P : Measure Seed) [IsProbabilityMeasure P] {m₀ m₁ : X → E}
    (h₀ : Measurable m₀) (h₁ : Measurable m₁) {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    (∫ h, gaussianPathLikelihood A m₀ m₁ σ n h
      ∂A.historyLaw P (gaussianResponseKernel m₀ h₀ σ) n) = 1 := by
  induction n with
  | zero => simp [gaussianPathLikelihood, AdaptiveKernel.Policy.historyLaw_zero]
  | succ n ih =>
    rw [gaussian_historyLaw_succ A P h₀ σ n,
      integral_map_of_stronglyMeasurable (gaussianStateStep_measurable A h₀ σ n)
        (gaussianPathLikelihood_measurable A h₀ h₁ σ (n + 1)).stronglyMeasurable]
    simp_rw [gaussianPathLikelihood_step A m₀ m₁ hσ n]
    rw [likelihoodStep_mean (gaussianPathLikelihood_measurable A h₀ h₁ σ n)
      (gaussianMeanGap_measurable A h₀ h₁ σ n)
      (gaussianPathLikelihood_integrable A P h₀ h₁ hσ n), ih]

theorem gaussianPathLikelihood_square_integrable (A : AdaptiveKernel.Policy Seed X E Y T)
    (P : Measure Seed) [IsProbabilityMeasure P] {m₀ m₁ : X → E}
    (h₀ : Measurable m₀) (h₁ : Measurable m₁) {σ C : ℝ} (hσ : σ ≠ 0)
    (hbound : ∀ x, ‖σ⁻¹ • (m₁ x - m₀ x)‖ ^ 2 ≤ C) (n : ℕ) :
    Integrable (fun h ↦ gaussianPathLikelihood A m₀ m₁ σ n h ^ 2)
      (A.historyLaw P (gaussianResponseKernel m₀ h₀ σ) n) := by
  induction n with
  | zero => simpa only [gaussianPathLikelihood, one_pow] using (integrable_const (1 : ℝ) (μ := P))
  | succ n ih =>
    rw [gaussian_historyLaw_succ A P h₀ σ n]
    apply (integrable_map_measure
      ((gaussianPathLikelihood_measurable A h₀ h₁ σ (n + 1)).pow_const 2).aestronglyMeasurable
      (gaussianStateStep_measurable A h₀ σ n).aemeasurable).mpr
    simpa only [Function.comp_def, gaussianPathLikelihood_step A m₀ m₁ hσ n] using
      likelihoodStep_square_integrable (gaussianPathLikelihood_measurable A h₀ h₁ σ n)
        (gaussianMeanGap_measurable A h₀ h₁ σ n) ih (fun h ↦ hbound (A.query n h))

/-- Uniform pointwise mean separation controls the entire adaptive likelihood. -/
theorem gaussianPathLikelihood_second_le (A : AdaptiveKernel.Policy Seed X E Y T)
    (P : Measure Seed) [IsProbabilityMeasure P] {m₀ m₁ : X → E}
    (h₀ : Measurable m₀) (h₁ : Measurable m₁) {σ C : ℝ} (hσ : σ ≠ 0)
    (hbound : ∀ x, ‖σ⁻¹ • (m₁ x - m₀ x)‖ ^ 2 ≤ C) (n : ℕ) :
    (∫ h, gaussianPathLikelihood A m₀ m₁ σ n h ^ 2
      ∂A.historyLaw P (gaussianResponseKernel m₀ h₀ σ) n) ≤ Real.exp ((n : ℝ) * C) := by
  induction n with
  | zero => simp [gaussianPathLikelihood, AdaptiveKernel.Policy.historyLaw_zero]
  | succ n ih =>
    rw [gaussian_historyLaw_succ A P h₀ σ n,
      integral_map_of_stronglyMeasurable (gaussianStateStep_measurable A h₀ σ n)
        ((gaussianPathLikelihood_measurable A h₀ h₁ σ (n + 1)).pow_const 2).stronglyMeasurable]
    simp_rw [gaussianPathLikelihood_step A m₀ m₁ hσ n]
    calc
      _ ≤ Real.exp C * (∫ h, gaussianPathLikelihood A m₀ m₁ σ n h ^ 2
          ∂A.historyLaw P (gaussianResponseKernel m₀ h₀ σ) n) :=
        likelihoodStep_second_le (gaussianPathLikelihood_measurable A h₀ h₁ σ n)
          (gaussianMeanGap_measurable A h₀ h₁ σ n)
          (gaussianPathLikelihood_square_integrable A P h₀ h₁ hσ hbound n)
          (fun h ↦ hbound (A.query n h))
      _ ≤ Real.exp C * Real.exp ((n : ℝ) * C) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos C).le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * C) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

/-- Actual adaptive Gaussian transcript testing, for arbitrary measurable seeds and tests. -/
theorem adaptive_gaussian_testing_lower (A : AdaptiveKernel.Policy Seed X E Y T)
    (P : Measure Seed) [IsProbabilityMeasure P] {m₀ m₁ : X → E}
    (h₀ : Measurable m₀) (h₁ : Measurable m₁) {σ C : ℝ} (hσ : σ ≠ 0)
    (hbound : ∀ x, ‖σ⁻¹ • (m₁ x - m₀ x)‖ ^ 2 ≤ C)
    (hsmall : Real.exp ((T : ℝ) * C) ≤ (65 / 64 : ℝ))
    {B : Set (AdaptiveKernel.History Seed E T)} (hB : MeasurableSet B) :
    (7 / 8 : ℝ) ≤
      (A.historyLaw P (gaussianResponseKernel m₀ h₀ σ) T).real B +
      (A.historyLaw P (gaussianResponseKernel m₁ h₁ σ) T).real Bᶜ := by
  exact likelihood_binary_testing_lower
    (gaussianPathLikelihood_measurable A h₀ h₁ σ T)
    (gaussianPathLikelihood_nonneg A m₀ m₁ σ T)
    (gaussianPathLikelihood_square_integrable A P h₀ h₁ hσ hbound T)
    (gaussianPathLikelihood_mean A P h₀ h₁ hσ T)
    ((gaussianPathLikelihood_second_le A P h₀ h₁ hσ hbound T).trans hsmall)
    (gaussian_historyLaw_likelihood A P h₀ h₁ hσ T) hB

end
end HeavyTail.GaussianLower
