import NoisyZO.AdaptiveKLSum
import NoisyZO.AssouadTesting
import NoisyZO.GaussianKernel
import NoisyZO.GaussianTranscript

/-!
# Summing adaptive Gaussian conditional KL costs

The history law at time `t` may depend on the hidden hypercube vertex `s`, but
not on the neighboring coordinate `i`.  This is the measure-theoretic reason
that the squared neighboring signals can be summed pointwise before taking the
expectation over the adaptive history.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace NoisyZO

theorem gaussian_conditional_KL_total_bound
    {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (history : Hypercube d → Fin T → Measure α)
    [hprob : ∀ s t, IsProbabilityMeasure (history s t)]
    (mean₁ mean₂ : Hypercube d → Fin d → Fin T → α → ℝ)
    (hmean₁ : ∀ s i t, Measurable (mean₁ s i t))
    (hmean₂ : ∀ s i t, Measurable (mean₂ s i t))
    (hint : ∀ s i t,
      Integrable (fun a ↦ (mean₁ s i t a - mean₂ s i t a) ^ 2 / 2) (history s t))
    (C : ℝ)
    (hsignal : ∀ s t a,
      ∑ i : Fin d, (mean₁ s i t a - mean₂ s i t a) ^ 2 ≤ C) :
    (∑ s : Hypercube d, ∑ i : Fin d, ∑ t : Fin T,
      (InformationTheory.klDiv
        (history s t ⊗ₘ gaussianOracleKernel (mean₁ s i t) (hmean₁ s i t))
        (history s t ⊗ₘ gaussianOracleKernel (mean₂ s i t) (hmean₂ s i t))).toReal) ≤
      (2 : ℝ) ^ d * T * C / 2 := by
  have hstep (s : Hypercube d) (t : Fin T) :
      (∑ i : Fin d,
        (InformationTheory.klDiv
          (history s t ⊗ₘ gaussianOracleKernel (mean₁ s i t) (hmean₁ s i t))
          (history s t ⊗ₘ gaussianOracleKernel (mean₂ s i t) (hmean₂ s i t))).toReal) ≤
        C / 2 := by
    simp_rw [klDiv_gaussianOracle_compProd_sameBase_toReal
      (history s t) _ _ _ _ (hint s _ t)]
    have hsumInt : Integrable
        (fun a ↦ ∑ i : Fin d, (mean₁ s i t a - mean₂ s i t a) ^ 2 / 2)
        (history s t) :=
      integrable_finsetSum Finset.univ fun i _ ↦ hint s i t
    rw [← integral_finsetSum Finset.univ (fun i _ ↦ hint s i t)]
    calc
      (∫ a, ∑ i : Fin d, (mean₁ s i t a - mean₂ s i t a) ^ 2 / 2 ∂history s t) ≤
          ∫ _a, C / 2 ∂history s t := by
            refine integral_mono_ae hsumInt (integrable_const (C / 2)) ?_
            filter_upwards with a
            have hs := hsignal s t a
            calc
              (∑ i : Fin d, (mean₁ s i t a - mean₂ s i t a) ^ 2 / 2) =
                  (∑ i : Fin d, (mean₁ s i t a - mean₂ s i t a) ^ 2) / 2 := by
                    rw [Finset.sum_div]
              _ ≤ C / 2 := div_le_div_of_nonneg_right hs (by norm_num)
      _ = C / 2 := by simp
  calc
    (∑ s : Hypercube d, ∑ i : Fin d, ∑ t : Fin T,
      (InformationTheory.klDiv
        (history s t ⊗ₘ gaussianOracleKernel (mean₁ s i t) (hmean₁ s i t))
        (history s t ⊗ₘ gaussianOracleKernel (mean₂ s i t) (hmean₂ s i t))).toReal) =
        ∑ s : Hypercube d, ∑ t : Fin T, ∑ i : Fin d,
          (InformationTheory.klDiv
            (history s t ⊗ₘ gaussianOracleKernel (mean₁ s i t) (hmean₁ s i t))
            (history s t ⊗ₘ gaussianOracleKernel (mean₂ s i t) (hmean₂ s i t))).toReal := by
              apply Finset.sum_congr rfl
              intro s _
              rw [Finset.sum_comm]
    _ ≤ ∑ _s : Hypercube d, ∑ _t : Fin T, C / 2 := by
          apply Finset.sum_le_sum
          intro s _
          exact Finset.sum_le_sum fun t _ ↦ hstep s t
    _ = (2 : ℝ) ^ d * T * C / 2 := by
          simp
          ring

/-- Full finite-transcript Gaussian KL sum over all directed hypercube edges. -/
theorem adaptive_gaussian_edge_KL_total_bound
    {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (mean : Hypercube d → ℕ → α → ℝ)
    (hmean : ∀ s t, Measurable (mean s t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (hint : ∀ s i t,
      Integrable (fun a ↦
        (mean s t a - mean (flipHypercube s i) t a) ^ 2 / 2)
        (adaptiveGaussianLaw μ₀ (mean s) (hmean s) update hupdate t))
    (C : ℝ)
    (hsignal : ∀ s (t : Fin T) a,
      ∑ i : Fin d,
        (mean s t a - mean (flipHypercube s i) t a) ^ 2 ≤ C) :
    (∑ s : Hypercube d, ∑ i : Fin d,
      (InformationTheory.klDiv
        (adaptiveGaussianLaw μ₀ (mean s) (hmean s) update hupdate T)
        (adaptiveGaussianLaw μ₀ (mean (flipHypercube s i))
          (hmean (flipHypercube s i)) update hupdate T)).toReal) ≤
      (2 : ℝ) ^ d * T * C / 2 := by
  let P : Hypercube d → ℕ → Measure α := fun s ↦
    adaptiveGaussianLaw μ₀ (mean s) (hmean s) update hupdate
  have hedge (s : Hypercube d) (i : Fin d) :
      (InformationTheory.klDiv (P s T) (P (flipHypercube s i) T)).toReal ≤
        ∑ t : Fin T,
          ∫ a, (mean s t a - mean (flipHypercube s i) t a) ^ 2 / 2 ∂P s t := by
    have h := adaptiveGaussianLaw_kl_toReal_le μ₀ μ₀
      (mean s) (mean (flipHypercube s i))
      (hmean s) (hmean (flipHypercube s i)) update hupdate
      (by simp [InformationTheory.klDiv_self])
      (fun t ↦ hint s i t) T
    calc
      (InformationTheory.klDiv (P s T) (P (flipHypercube s i) T)).toReal ≤
          ∑ t ∈ Finset.range T,
            ∫ a, (mean s t a - mean (flipHypercube s i) t a) ^ 2 / 2 ∂P s t := by
              simpa only [P, InformationTheory.klDiv_self, ENNReal.toReal_zero, zero_add] using h
      _ = ∑ t : Fin T,
            ∫ a, (mean s t a - mean (flipHypercube s i) t a) ^ 2 / 2 ∂P s t := by
              exact (Fin.sum_univ_eq_sum_range
                (fun t : ℕ ↦
                  ∫ a, (mean s t a - mean (flipHypercube s i) t a) ^ 2 / 2 ∂P s t) T).symm
  let _ : ∀ s (t : Fin T), IsProbabilityMeasure (P s t) := fun s t ↦
    adaptiveGaussianLaw_isProbability μ₀ (mean s) (hmean s) update hupdate t
  have htotal := gaussian_conditional_KL_total_bound
    (d := d) (T := T)
    (fun s t ↦ P s t)
    (fun s i t ↦ mean s t)
    (fun s i t ↦ mean (flipHypercube s i) t)
    (fun s i t ↦ hmean s t)
    (fun s i t ↦ hmean (flipHypercube s i) t)
    (fun s i t ↦ hint s i t) C hsignal
  calc
    (∑ s : Hypercube d, ∑ i : Fin d,
      (InformationTheory.klDiv (P s T) (P (flipHypercube s i) T)).toReal) ≤
        ∑ s : Hypercube d, ∑ i : Fin d, ∑ t : Fin T,
          (InformationTheory.klDiv
            (P s t ⊗ₘ gaussianOracleKernel (mean s t) (hmean s t))
            (P s t ⊗ₘ gaussianOracleKernel
              (mean (flipHypercube s i) t) (hmean (flipHypercube s i) t))).toReal := by
                apply Finset.sum_le_sum
                intro s _
                apply Finset.sum_le_sum
                intro i _
                calc
                  (InformationTheory.klDiv (P s T) (P (flipHypercube s i) T)).toReal ≤
                      ∑ t : Fin T,
                        ∫ a, (mean s t a - mean (flipHypercube s i) t a) ^ 2 / 2
                          ∂P s t := hedge s i
                  _ = ∑ t : Fin T,
                      (InformationTheory.klDiv
                        (P s t ⊗ₘ gaussianOracleKernel (mean s t) (hmean s t))
                        (P s t ⊗ₘ gaussianOracleKernel
                          (mean (flipHypercube s i) t)
                          (hmean (flipHypercube s i) t))).toReal := by
                            apply Finset.sum_congr rfl
                            intro t _
                            symm
                            exact klDiv_gaussianOracle_compProd_sameBase_toReal
                              (P s t) (mean s t) (mean (flipHypercube s i) t)
                              (hmean s t) (hmean (flipHypercube s i) t) (hint s i t)
    _ ≤ (2 : ℝ) ^ d * T * C / 2 := htotal

end NoisyZO
