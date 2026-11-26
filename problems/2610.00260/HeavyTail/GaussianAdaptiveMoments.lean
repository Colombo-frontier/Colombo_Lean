import HeavyTail.GaussianAdaptiveLower

/-! Unbiasedness, integrability and both centered moments of the actual
Gaussian response kernel used in the adaptive history laws. -/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace HeavyTail.GaussianLower
noncomputable section

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace X]

theorem gaussianResponseKernel_integrable (mean : X → E) (hm : Measurable mean)
    (σ : ℝ) (x : X) : Integrable (fun y ↦ y) (gaussianResponseKernel mean hm σ x) := by
  unfold gaussianResponseKernel
  rw [kernelOfSampler_apply]
  have hF : Measurable (fun z : E ↦ mean x + σ • z) := by fun_prop
  apply (integrable_map_measure measurable_id.aestronglyMeasurable hF.aemeasurable).mpr
  exact (integrable_const (mean x)).add ((gaussian_id_integrable E).smul σ)

theorem gaussianResponseKernel_unbiased (mean : X → E) (hm : Measurable mean)
    (σ : ℝ) (x : X) :
    (∫ y, y ∂gaussianResponseKernel mean hm σ x) = mean x := by
  unfold gaussianResponseKernel
  rw [kernelOfSampler_apply]
  have hF : Measurable (fun z : E ↦ mean x + σ • z) := by fun_prop
  rw [integral_map_of_stronglyMeasurable hF
    (show StronglyMeasurable (fun y : E ↦ y) from stronglyMeasurable_id)]
  have hi : Integrable (fun z : E ↦ σ • z) (GaussianEstimates.euclideanGaussianLaw E) :=
    (gaussian_id_integrable E).smul σ
  rw [integral_add (integrable_const _) hi, integral_const, integral_smul, gaussian_vector_mean_zero]
  simp

theorem gaussianResponseKernel_two_moment {mean : X → E} (hm : Measurable mean)
    {σ L s p : ℝ} (hL : 0 ≤ L) (hs : 0 ≤ s) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (htrace : σ ^ 2 * Module.finrank ℝ E ≤ L ^ 2) (hdir : σ ^ 2 ≤ s ^ 2) (x : X) :
    (∫ y, ‖y - mean x‖ ^ p ∂gaussianResponseKernel mean hm σ x) ≤ L ^ p ∧
    ∀ w : E, ‖w‖ = 1 →
      (∫ y, |⟪w, y - mean x⟫_ℝ| ^ p ∂gaussianResponseKernel mean hm σ x) ≤ s ^ p := by
  have hbase := gaussian_two_moment_admissible E hL hs hp hp2 htrace hdir
  have hF : Measurable (fun z : E ↦ mean x + σ • z) := by fun_prop
  constructor
  · unfold gaussianResponseKernel
    rw [kernelOfSampler_apply, integral_map_of_stronglyMeasurable hF
      (show StronglyMeasurable (fun y : E ↦ ‖y - mean x‖ ^ p) from
        ((Real.continuous_rpow_const hp).comp (continuous_id.sub continuous_const).norm).stronglyMeasurable)]
    simpa only [add_sub_cancel_left] using hbase.1
  · intro w hw
    unfold gaussianResponseKernel
    rw [kernelOfSampler_apply, integral_map_of_stronglyMeasurable hF
      (show StronglyMeasurable (fun y : E ↦ |⟪w, y - mean x⟫_ℝ| ^ p) from
        ((Real.continuous_rpow_const hp).comp
          ((continuous_const.inner (continuous_id.sub continuous_const)).abs)).stronglyMeasurable)]
    simpa only [add_sub_cancel_left] using hbase.2 w hw

theorem traceKernel_two_moment {k : ℕ} (hk : 0 < k) {L s p : ℝ}
    (hL : 0 ≤ L) (hs : 0 ≤ s) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hdim : L ^ 2 ≤ (k : ℝ) * s ^ 2) (a ρ : ℝ) (v : Fin k → Bool) (x : HardSpace k) :
    (∫ y, ‖y - hardGradient a ρ (gaussianSigns v) x‖ ^ p
      ∂traceKernel a ρ (L / Real.sqrt k) v x) ≤ L ^ p ∧
    ∀ w : HardSpace k, ‖w‖ = 1 →
      (∫ y, |⟪w, y - hardGradient a ρ (gaussianSigns v) x⟫_ℝ| ^ p
        ∂traceKernel a ρ (L / Real.sqrt k) v x) ≤ s ^ p := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hvar : (L / Real.sqrt (k : ℝ)) ^ 2 = L ^ 2 / k := by
    rw [div_pow, Real.sq_sqrt hkR.le]
  apply gaussianResponseKernel_two_moment (hardGradient_measurable a ρ (gaussianSigns v)) hL hs hp hp2
  · rw [hvar]
    simp only [HardSpace, finrank_euclideanSpace_fin]
    exact le_of_eq (div_mul_cancel₀ _ hkR.ne')
  · rw [hvar]
    exact (div_le_iff₀ hkR).mpr (by simpa only [mul_comm] using hdim)

end
end HeavyTail.GaussianLower

