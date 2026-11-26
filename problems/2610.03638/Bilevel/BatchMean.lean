import Bilevel.StochasticInner
import Bilevel.Clipping

/-!
# Fresh-batch mean and correction errors

Actual sample means of Hilbert-valued L2 martingale differences have zero
Bochner mean and MSE at most `σ²/n`. The proof derives cross-term orthogonality
from conditional centering. A measurable correction that improves pointwise
error, or a nonexpansive map fixing the true mean, preserves the MSE bound.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Bilevel.BatchMean

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

def sampleMean (ξ : ℕ → Lp E 2 μ) (n : ℕ) (ω : Ω) : E :=
  (1 / (n : ℝ)) • ∑ i ∈ Finset.range n, ξ i ω

def meanLp (ξ : ℕ → Lp E 2 μ) (n : ℕ) : Lp E 2 μ :=
  (1 / (n : ℝ)) • ∑ i ∈ Finset.range n, ξ i

theorem coe_mean_ae (ξ : ℕ → Lp E 2 μ) (n : ℕ) :
    (meanLp ξ n : Ω → E) =ᵐ[μ] sampleMean ξ n := by
  filter_upwards [Lp.coeFn_smul (1 / (n : ℝ)) (∑ i ∈ Finset.range n, ξ i),
    InexactHorner.coe_sum_ae (m0 := m0) ξ (Finset.range n)] with ω hsmul hsum
  simp only [meanLp, sampleMean, hsmul, Pi.smul_apply, hsum]

section Centered
variable [CompleteSpace E]

theorem errors_orthogonal
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0) (ξ : ℕ → Lp E 2 μ)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (ξ i) μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (ξ j) : Lp E 2 μ) = 0)
    {i j : ℕ} (hij : i ≠ j) : inner (𝕜 := ℝ) (ξ i) (ξ j) = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [real_inner_comm]
    exact InexactHorner.condMean_zero_inner (m0 := m0) (hle j) _ _ (centered j) (adapted i j h)
  · exact InexactHorner.condMean_zero_inner (m0 := m0) (hle i) _ _ (centered i) (adapted j i h)

theorem meanLp_variance
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0) (ξ : ℕ → Lp E 2 μ)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (ξ i) μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (ξ j) : Lp E 2 μ) = 0) (n : ℕ) :
    StochasticInner.risk (meanLp ξ n) = (1 / (n : ℝ)) ^ 2 *
      ∑ i ∈ Finset.range n, StochasticInner.risk (ξ i) := by
  simp only [StochasticInner.risk_eq_norm_sq, meanLp, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  rw [InexactHorner.orthogonal_sum_sq (Finset.range n) ξ
    (fun _ _ _ _ hij => errors_orthogonal past hle ξ adapted centered hij)]

theorem sampleMean_mse
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0) (ξ : ℕ → Lp E 2 μ)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (ξ i) μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (ξ j) : Lp E 2 μ) = 0)
    (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (variance : ∀ i < n, StochasticInner.risk (ξ i) ≤ σ ^ 2) :
    (∫ ω, ‖sampleMean ξ n ω‖ ^ 2 ∂μ) ≤ σ ^ 2 / (n : ℝ) := by
  have heq : (∫ ω, ‖sampleMean ξ n ω‖ ^ 2 ∂μ) = StochasticInner.risk (meanLp ξ n) := by
    apply integral_congr_ae
    filter_upwards [coe_mean_ae ξ n] with ω hω
    rw [hω]
  rw [heq, meanLp_variance past hle ξ adapted centered]
  calc
    _ ≤ (1 / (n : ℝ)) ^ 2 * ∑ _i ∈ Finset.range n, σ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i hi => variance i (Finset.mem_range.mp hi))) (sq_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hnc : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
      ring

theorem centered_integral [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m0) (ξ : Lp E 2 μ)
    (centered : (condExpL2 E ℝ hm ξ : Lp E 2 μ) = 0) : (∫ ω, ξ ω ∂μ) = 0 := by
  have hc := integral_condExpL2_eq (𝕜 := ℝ) hm ξ (@MeasurableSet.univ Ω m)
    (measure_ne_top μ Set.univ)
  have hzero : (fun ω => (condExpL2 E ℝ hm ξ : Lp E 2 μ) ω) =ᵐ[μ] fun _ => (0 : E) := by
    rw [centered]
    exact Lp.coeFn_zero E 2 μ
  have heq : (∫ ω, (condExpL2 E ℝ hm ξ : Lp E 2 μ) ω ∂μ) = ∫ ω, ξ ω ∂μ := by
    simpa only [Measure.restrict_univ] using hc
  rw [← heq, integral_congr_ae hzero]
  simp

theorem sampleMean_unbiased [IsFiniteMeasure μ]
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0) (ξ : ℕ → Lp E 2 μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (ξ j) : Lp E 2 μ) = 0) (n : ℕ) :
    (∫ ω, sampleMean ξ n ω ∂μ) = 0 := by
  unfold sampleMean
  rw [integral_smul, integral_finset_sum]
  · simp only [centered_integral (hle _) _ (centered _), Finset.sum_const_zero, smul_zero]
  · intro i _
    exact (Lp.memLp (ξ i)).integrable (by norm_num)

omit [CompleteSpace E] in
theorem sampleMean_integrable [IsFiniteMeasure μ] (ξ : ℕ → Lp E 2 μ) (n : ℕ) :
    Integrable (sampleMean ξ n) μ := by
  apply Integrable.smul
  apply integrable_finset_sum
  intro i _
  exact (Lp.memLp (ξ i)).integrable (by norm_num)

theorem shifted_sampleMean_unbiased [IsProbabilityMeasure μ]
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0) (ξ : ℕ → Lp E 2 μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (ξ j) : Lp E 2 μ) = 0)
    (n : ℕ) (truth : E) : (∫ ω, truth + sampleMean ξ n ω ∂μ) = truth := by
  rw [integral_add (integrable_const truth) (sampleMean_integrable ξ n),
    sampleMean_unbiased past hle ξ centered]
  simp

end Centered

/-- A measurable corrected estimator dominated by the original error has no
larger MSE. This requires only pointwise error improvement, not a globally
nonexpansive correction map; it can be instantiated by radial clipping. -/
theorem measurable_correction_mse_le
    (truth : E) (error : Lp E 2 μ) (corrected : Ω → E)
    (hmeas : AEStronglyMeasurable corrected μ)
    (improvement : ∀ᵐ ω ∂μ, ‖corrected ω - truth‖ ≤ ‖error ω‖) :
    (∫ ω, ‖corrected ω - truth‖ ^ 2 ∂μ) ≤ StochasticInner.risk error := by
  have hsq : ∀ᵐ ω ∂μ, ‖corrected ω - truth‖ ^ 2 ≤ ‖error ω‖ ^ 2 := by
    filter_upwards [improvement] with ω hω
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hω
  have hfun : Continuous (fun z : E => ‖z - truth‖ ^ 2) := by fun_prop
  have hdom : ∀ᵐ ω ∂μ, ‖‖corrected ω - truth‖ ^ 2‖ ≤ ‖error ω‖ ^ 2 := by
    filter_upwards [hsq] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω
  have hint := (StochasticInner.integrable_norm_sq error).mono'
    (hfun.comp_aestronglyMeasurable hmeas) hdom
  exact integral_mono_ae hint (StochasticInner.integrable_norm_sq error) hsq

/-- A nonexpansive correction fixing the true mean cannot increase its MSE.
Integrability of the corrected squared error is proved by domination. -/
theorem corrected_mse_le
    (correct : E → E) (nonexpansive : LipschitzWith 1 correct)
    (truth : E) (fixed : correct truth = truth) (error : Lp E 2 μ) :
    (∫ ω, ‖correct (truth + error ω) - truth‖ ^ 2 ∂μ) ≤ StochasticInner.risk error := by
  have hn : ∀ ω, ‖correct (truth + error ω) - truth‖ ≤ ‖error ω‖ := by
    intro ω
    have h := nonexpansive.dist_le_mul (truth + error ω) truth
    simpa only [fixed, dist_eq_norm, add_sub_cancel_left, NNReal.coe_one, one_mul] using h
  have hsq : ∀ ω, ‖correct (truth + error ω) - truth‖ ^ 2 ≤ ‖error ω‖ ^ 2 := by
    intro ω
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hn ω)
  have hcont : Continuous correct := nonexpansive.continuous
  have hfun : Continuous (fun z : E => ‖correct (truth + z) - truth‖ ^ 2) := by fun_prop
  have hmeas := hfun.comp_aestronglyMeasurable (Lp.aestronglyMeasurable error)
  have hdom : ∀ᵐ ω ∂μ, ‖‖correct (truth + error ω) - truth‖ ^ 2‖ ≤ ‖error ω‖ ^ 2 := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq ω
  have hint : Integrable (fun ω => ‖correct (truth + error ω) - truth‖ ^ 2) μ :=
    (StochasticInner.integrable_norm_sq error).mono' hmeas hdom
  exact integral_mono hint (StochasticInner.integrable_norm_sq error) hsq

theorem corrected_sampleMean_mse [CompleteSpace E]
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0) (ξ : ℕ → Lp E 2 μ)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (ξ i) μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (ξ j) : Lp E 2 μ) = 0)
    (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (variance : ∀ i < n, StochasticInner.risk (ξ i) ≤ σ ^ 2)
    (correct : E → E) (nonexpansive : LipschitzWith 1 correct)
    (truth : E) (fixed : correct truth = truth) :
    (∫ ω, ‖correct (truth + sampleMean ξ n ω) - truth‖ ^ 2 ∂μ) ≤ σ ^ 2 / (n : ℝ) := by
  have hmean : StochasticInner.risk (meanLp ξ n) = ∫ ω, ‖sampleMean ξ n ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [coe_mean_ae ξ n] with ω hω
    rw [hω]
  have hc := corrected_mse_le correct nonexpansive truth fixed (meanLp ξ n)
  have heq : (∫ ω, ‖correct (truth + sampleMean ξ n ω) - truth‖ ^ 2 ∂μ) =
      ∫ ω, ‖correct (truth + (meanLp ξ n) ω) - truth‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [coe_mean_ae ξ n] with ω hω
    rw [hω]
  rw [heq]
  exact hc.trans (hmean ▸ sampleMean_mse past hle ξ adapted centered n hn σ variance)

/-- Measurability of the actual radial clipping map composed with a strongly
measurable estimator. The scalar division is measurable also at zero. -/
theorem clip_stronglyMeasurable (C : ℝ) {f : Ω → E} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun ω => Clipping.clip C (f ω)) := by
  have hcoef : StronglyMeasurable (fun ω => C / ‖f ω‖) :=
    (measurable_const.div hf.norm.measurable).stronglyMeasurable
  exact StronglyMeasurable.ite (measurableSet_le hf.norm.measurable measurable_const)
    hf (hcoef.smul hf)

theorem radial_clip_mse_le (C : ℝ) (hC : 0 ≤ C) (truth : E) (htruth : ‖truth‖ ≤ C)
    (error : Lp E 2 μ) :
    (∫ ω, ‖Clipping.clip C (truth + error ω) - truth‖ ^ 2 ∂μ) ≤ StochasticInner.risk error := by
  apply measurable_correction_mse_le truth error (fun ω => Clipping.clip C (truth + error ω))
  · exact (clip_stronglyMeasurable C
      (stronglyMeasurable_const.add (Lp.stronglyMeasurable error))).aestronglyMeasurable
  · filter_upwards with ω
    simpa only [add_sub_cancel_left] using
      Clipping.error_nonincreasing C hC (truth + error ω) truth htruth

/-- Actual projected fresh-batch MSE, with radial clipping and its
measurability proved in this development. -/
theorem radial_clipped_sampleMean_mse [CompleteSpace E]
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ m0) (ξ : ℕ → Lp E 2 μ)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (ξ i) μ)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (ξ j) : Lp E 2 μ) = 0)
    (n : ℕ) (hn : 0 < n) (σ : ℝ)
    (variance : ∀ i < n, StochasticInner.risk (ξ i) ≤ σ ^ 2)
    (C : ℝ) (hC : 0 ≤ C) (truth : E) (htruth : ‖truth‖ ≤ C) :
    (∫ ω, ‖Clipping.clip C (truth + sampleMean ξ n ω) - truth‖ ^ 2 ∂μ) ≤ σ ^ 2 / (n : ℝ) := by
  have heq : (∫ ω, ‖Clipping.clip C (truth + sampleMean ξ n ω) - truth‖ ^ 2 ∂μ) =
      ∫ ω, ‖Clipping.clip C (truth + (meanLp ξ n) ω) - truth‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [coe_mean_ae ξ n] with ω hω
    rw [hω]
  have hmean : StochasticInner.risk (meanLp ξ n) = ∫ ω, ‖sampleMean ξ n ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [coe_mean_ae ξ n] with ω hω
    rw [hω]
  rw [heq]
  have hc := radial_clip_mse_le C hC truth htruth (meanLp ξ n)
  rw [hmean] at hc
  exact hc.trans (sampleMean_mse past hle ξ adapted centered n hn σ variance)

end Bilevel.BatchMean
