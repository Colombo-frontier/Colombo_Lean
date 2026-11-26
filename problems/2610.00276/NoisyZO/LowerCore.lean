import NoisyZO.HardGaussianLower
import NoisyZO.LowerRate

/-!
# End-to-end adaptive lower-rate assembly

This module chooses the saturated bandwidth, verifies the information budget,
runs the concrete adaptive Gaussian Assouad theorem, and converts Hamming loss
to the manuscript's optimization-rate lower bound.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace NoisyZO

noncomputable section

/-- Complete lower-rate assembly for the explicit hard responses.  The
decision-theoretic premises name the estimator's coordinate errors, total
variation/Pinsker bound, and strong-convexity conversion; all bandwidth,
adaptive-Gaussian KL, hypercube averaging, and rate arithmetic are internal. -/
theorem hard_family_adaptive_gaussian_lower_rate
    {α : Type*} [MeasurableSpace α] {d T : ℕ}
    (hd : 0 < d) (hT : 0 < T)
    (β a : ℝ) (hβ : 2 < β) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (err tv : Hypercube d → Fin d → ℝ) (risk : Hypercube d → ℝ)
    (hedge : ∀ s i,
      1 - tv s i ≤ err s i + err (flipHypercube s i) i)
    (hpinsker : ∀ s i,
      tv s i ≤ Real.sqrt
        ((InformationTheory.klDiv
          (adaptiveGaussianLaw μ₀
            (hardGaussianMean
              (a * lowerBandwidth a d T β ^ (β - 1))
              (lowerBandwidth a d T β)
              (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
                (lt_trans (by norm_num) hβ)) query s)
            (hardGaussianMean_measurable
              (a * lowerBandwidth a d T β ^ (β - 1))
              (lowerBandwidth a d T β)
              (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
                (lt_trans (by norm_num) hβ)) query hquery s)
            update hupdate T)
          (adaptiveGaussianLaw μ₀
            (hardGaussianMean
              (a * lowerBandwidth a d T β ^ (β - 1))
              (lowerBandwidth a d T β)
              (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
                (lt_trans (by norm_num) hβ)) query (flipHypercube s i))
            (hardGaussianMean_measurable
              (a * lowerBandwidth a d T β ^ (β - 1))
              (lowerBandwidth a d T β)
              (lowerBandwidth_pos ha (by exact_mod_cast hd) (by exact_mod_cast hT)
                (lt_trans (by norm_num) hβ)) query hquery (flipHypercube s i))
            update hupdate T)).toReal / 2))
    (hpoint : ∀ s,
      ((((a * lowerBandwidth a d T β ^ (β - 1)) /
          (2 * Real.sqrt d)) ^ 2) / 2) *
        (∑ i : Fin d, err s i) ≤ risk s) :
    (3 * a ^ 2 / 64) *
        min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent β) ≤
      (∑ s : Hypercube d, risk s) / (2 : ℝ) ^ d := by
  let h : ℝ := lowerBandwidth a d T β
  let c : ℝ := a * h ^ (β - 1)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
  have hβ0 : 0 < β := lt_trans (by norm_num) hβ
  have hh : 0 < h := lowerBandwidth_pos ha hdR hTR hβ0
  have hrpowSq : (h ^ (β - 1)) ^ (2 : ℕ) = h ^ (2 * β - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hh)]
    congr 1
    norm_num
    ring
  have hrpowBudget :
      (h ^ (β - 1)) ^ (2 : ℕ) * h ^ (2 : ℕ) = h ^ (2 * β) := by
    rw [hrpowSq, ← Real.rpow_natCast, ← Real.rpow_add hh]
    congr 1
    norm_num
  have hbudget : 2 * c ^ 2 * T * h ^ 2 / (d : ℝ) ^ 2 ≤ (1 / 8 : ℝ) := by
    calc
      2 * c ^ 2 * T * h ^ 2 / (d : ℝ) ^ 2 =
          2 * a ^ 2 * T *
            ((h ^ (β - 1)) ^ (2 : ℕ) * h ^ (2 : ℕ)) / (d : ℝ) ^ 2 := by
        dsimp only [c]
        rw [mul_pow]
        ring
      _ = 2 * a ^ 2 * T * h ^ (2 * β) / (d : ℝ) ^ 2 := by
        rw [hrpowBudget]
      _ ≤ (1 / 8 : ℝ) := by
        dsimp only [h]
        exact lowerBandwidth_KL_budget ha hdR hTR hβ0
  have hham : (2 : ℝ) ^ d * (3 * d / 8) ≤
      ∑ s : Hypercube d, ∑ i : Fin d, err s i := by
    apply hard_family_adaptive_gaussian_three_eighths hd μ₀ c h hh
      query hquery update hupdate err tv
    · exact hedge
    · intro s i
      simpa only [c, h] using hpinsker s i
    · exact hbudget
  have hloss : 3 * c ^ 2 / 64 ≤
      (∑ s : Hypercube d, risk s) / (2 : ℝ) ^ d := by
    apply hard_family_average_loss_three_over_sixty_four hd c err risk
    · intro s
      simpa only [c, h] using hpoint s
    · exact hham
  calc
    (3 * a ^ 2 / 64) *
        min 1 (((d : ℝ) ^ 2 / T) ^ rateExponent β) ≤
        (3 * a ^ 2 / 64) * h ^ (2 * β - 2) := by
      dsimp only [h]
      exact lower_loss_rate ha ha4 hdR hTR hβ
    _ = 3 * c ^ 2 / 64 := by
      dsimp only [c]
      rw [mul_pow, hrpowSq]
      ring
    _ ≤ (∑ s : Hypercube d, risk s) / (2 : ℝ) ^ d := hloss

end

end NoisyZO
