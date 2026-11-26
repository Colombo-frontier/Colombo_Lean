import NoisyZO.HardHypercube
import NoisyZO.GaussianAssouad
import NoisyZO.LowerConstants

/-!
# Concrete adaptive-Gaussian lower bound for the hard family

The explicit compactly supported hard family has a uniform pointwise signal
bound.  Consequently every squared Gaussian mean difference is integrable
under every probability history law.  This file feeds those facts into the
finite-transcript Assouad theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace NoisyZO

noncomputable section

theorem hardGaussianMean_edge_integrable
    {α : Type*} [MeasurableSpace α] {d : ℕ} (hd : 0 < d)
    (c h : ℝ) (hh : 0 < h) (query : ℕ → α → Point d)
    (hquery : ∀ t, Measurable (query t))
    (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Hypercube d) (i : Fin d) (t : ℕ) :
    Integrable (fun a ↦
      (hardGaussianMean c h hh query s t a -
        hardGaussianMean c h hh query (flipHypercube s i) t a) ^ 2 / 2) μ := by
  let C : ℝ := 4 * c ^ 2 * h ^ 2 / d
  have hmeas : Measurable (fun a ↦
      (hardGaussianMean c h hh query s t a -
        hardGaussianMean c h hh query (flipHypercube s i) t a) ^ 2 / 2) := by
    exact (((hardGaussianMean_measurable c h hh query hquery s t).sub
      (hardGaussianMean_measurable c h hh query hquery
        (flipHypercube s i) t)).pow_const 2).div_const 2
  refine (integrable_const (C / 2)).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with a
  have hone :
      (hardGaussianMean c h hh query s t a -
        hardGaussianMean c h hh query (flipHypercube s i) t a) ^ 2 ≤
        ∑ j : Fin d,
          (hardGaussianMean c h hh query s t a -
            hardGaussianMean c h hh query (flipHypercube s j) t a) ^ 2 := by
    exact Finset.single_le_sum
      (fun j _ ↦ sq_nonneg
        (hardGaussianMean c h hh query s t a -
          hardGaussianMean c h hh query (flipHypercube s j) t a))
      (Finset.mem_univ i)
  have hbound := hone.trans
    (hardGaussianMean_signal_sum_le hd c h hh query s t a)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right hbound (by norm_num)

/-- Every directed edge of the adaptive Gaussian hard family has finite KL divergence. -/
theorem hardAdaptiveGaussianLaw_edge_kl_ne_top
    {α : Type*} [MeasurableSpace α] {d T : ℕ} (hd : 0 < d)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (c h : ℝ) (hh : 0 < h)
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (s : Hypercube d) (i : Fin d) :
    InformationTheory.klDiv
        (adaptiveGaussianLaw μ₀
          (hardGaussianMean c h hh query s)
          (hardGaussianMean_measurable c h hh query hquery s)
          update hupdate T)
        (adaptiveGaussianLaw μ₀
          (hardGaussianMean c h hh query (flipHypercube s i))
          (hardGaussianMean_measurable c h hh query hquery (flipHypercube s i))
          update hupdate T) ≠ ∞ := by
  apply adaptiveGaussianLaw_kl_ne_top μ₀ μ₀
    (hardGaussianMean c h hh query s)
    (hardGaussianMean c h hh query (flipHypercube s i))
    (hardGaussianMean_measurable c h hh query hquery s)
    (hardGaussianMean_measurable c h hh query hquery (flipHypercube s i))
    update hupdate (by simp [InformationTheory.klDiv_self])
  intro t
  let _ : IsProbabilityMeasure
      (adaptiveGaussianLaw μ₀
        (hardGaussianMean c h hh query s)
        (hardGaussianMean_measurable c h hh query hquery s)
        update hupdate t) :=
    adaptiveGaussianLaw_isProbability μ₀
      (hardGaussianMean c h hh query s)
      (hardGaussianMean_measurable c h hh query hquery s)
      update hupdate t
  exact hardGaussianMean_edge_integrable hd c h hh query hquery _ s i t

/-- The lower-bound testing inequality specialized all the way to the explicit
hard-function responses and the recursive adaptive Gaussian transcript law. -/
theorem hard_family_adaptive_gaussian_assouad_bound
    {α : Type*} [MeasurableSpace α] {d T : ℕ} (hd : 0 < d)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (c h : ℝ) (hh : 0 < h)
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (err tv : Hypercube d → Fin d → ℝ)
    (hedge : ∀ s i,
      1 - tv s i ≤ err s i + err (flipHypercube s i) i)
    (hpinsker : ∀ s i,
      tv s i ≤ Real.sqrt
        ((InformationTheory.klDiv
          (adaptiveGaussianLaw μ₀
            (hardGaussianMean c h hh query s)
            (hardGaussianMean_measurable c h hh query hquery s)
            update hupdate T)
          (adaptiveGaussianLaw μ₀
            (hardGaussianMean c h hh query (flipHypercube s i))
            (hardGaussianMean_measurable c h hh query hquery
              (flipHypercube s i))
            update hupdate T)).toReal / 2)) :
    ((((2 : ℝ) ^ d * d) / 2) *
        (1 - Real.sqrt
          ((T * (4 * c ^ 2 * h ^ 2 / d) / (2 * d)) / 2))) ≤
      ∑ s : Hypercube d, ∑ i : Fin d, err s i := by
  let mean : Hypercube d → ℕ → α → ℝ :=
    fun s ↦ hardGaussianMean c h hh query s
  have hmean : ∀ s t, Measurable (mean s t) := by
    intro s t
    exact hardGaussianMean_measurable c h hh query hquery s t
  have hint : ∀ s i t,
      Integrable (fun a ↦
        (mean s t a - mean (flipHypercube s i) t a) ^ 2 / 2)
        (adaptiveGaussianLaw μ₀ (mean s) (hmean s) update hupdate t) := by
    intro s i t
    let _ : IsProbabilityMeasure
        (adaptiveGaussianLaw μ₀ (mean s) (hmean s) update hupdate t) :=
      adaptiveGaussianLaw_isProbability μ₀ (mean s) (hmean s) update hupdate t
    exact hardGaussianMean_edge_integrable hd c h hh query hquery
      (adaptiveGaussianLaw μ₀ (mean s) (hmean s) update hupdate t) s i t
  have hC : 0 ≤ 4 * c ^ 2 * h ^ 2 / (d : ℝ) := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    positivity
  apply adaptive_gaussian_assouad_bound hd μ₀ mean hmean update hupdate
    hint (4 * c ^ 2 * h ^ 2 / d) hC (err := err) (tv := tv)
  · intro s t a
    exact hardGaussianMean_signal_sum_le hd c h hh query s t a
  · exact hedge
  · intro s i
    simpa only [mean] using hpinsker s i

/-- Under the manuscript's `1/8` information budget, the explicit adaptive
Gaussian hard family forces at least `3d/8` average coordinate errors. -/
theorem hard_family_adaptive_gaussian_three_eighths
    {α : Type*} [MeasurableSpace α] {d T : ℕ} (hd : 0 < d)
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (c h : ℝ) (hh : 0 < h)
    (query : ℕ → α → Point d) (hquery : ∀ t, Measurable (query t))
    (update : ℕ → α × ℝ → α) (hupdate : ∀ t, Measurable (update t))
    (err tv : Hypercube d → Fin d → ℝ)
    (hedge : ∀ s i,
      1 - tv s i ≤ err s i + err (flipHypercube s i) i)
    (hpinsker : ∀ s i,
      tv s i ≤ Real.sqrt
        ((InformationTheory.klDiv
          (adaptiveGaussianLaw μ₀
            (hardGaussianMean c h hh query s)
            (hardGaussianMean_measurable c h hh query hquery s)
            update hupdate T)
          (adaptiveGaussianLaw μ₀
            (hardGaussianMean c h hh query (flipHypercube s i))
            (hardGaussianMean_measurable c h hh query hquery
              (flipHypercube s i))
            update hupdate T)).toReal / 2))
    (hbudget :
      2 * c ^ 2 * T * h ^ 2 / (d : ℝ) ^ 2 ≤ (1 / 8 : ℝ)) :
    (2 : ℝ) ^ d * (3 * d / 8) ≤
      ∑ s : Hypercube d, ∑ i : Fin d, err s i := by
  let Kbar : ℝ := T * (4 * c ^ 2 * h ^ 2 / d) / (2 * d)
  let N : ℝ := (2 : ℝ) ^ d * d
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hKbar : Kbar = 2 * c ^ 2 * T * h ^ 2 / (d : ℝ) ^ 2 := by
    dsimp [Kbar]
    field_simp [ne_of_gt hdR]
    ring
  have hK0 : 0 ≤ Kbar := by
    dsimp [Kbar]
    positivity
  have hK : Kbar ≤ (1 / 8 : ℝ) := by
    rw [hKbar]
    exact hbudget
  have hthree := assouad_three_eighths (N := N) (Kbar := Kbar)
    (by dsimp [N]; positivity) hK0 hK
  have hmain := hard_family_adaptive_gaussian_assouad_bound hd μ₀ c h hh
    query hquery update hupdate err tv hedge hpinsker
  calc
    (2 : ℝ) ^ d * (3 * d / 8) = 3 * N / 8 := by
      dsimp [N]
      ring
    _ ≤ N / 2 * (1 - Real.sqrt (Kbar / 2)) := hthree
    _ ≤ ∑ s : Hypercube d, ∑ i : Fin d, err s i := by
      simpa only [N, Kbar] using hmain

/-- Strong convexity converts the preceding Hamming lower bound to the exact
`3 c² / 64` average optimization-loss scale.  Here `c` is the perturbation
coefficient `a h^(β-1)` from the manuscript. -/
theorem hard_family_average_loss_three_over_sixty_four
    {d : ℕ} (hd : 0 < d) (c : ℝ)
    (err : Hypercube d → Fin d → ℝ) (risk : Hypercube d → ℝ)
    (hpoint : ∀ s,
      (((c / (2 * Real.sqrt d)) ^ 2) / 2) *
        (∑ i : Fin d, err s i) ≤ risk s)
    (hham : (2 : ℝ) ^ d * (3 * d / 8) ≤
      ∑ s : Hypercube d, ∑ i : Fin d, err s i) :
    3 * c ^ 2 / 64 ≤
      (∑ s : Hypercube d, risk s) / (2 : ℝ) ^ d := by
  have havg := averaged_hamming_to_loss risk
    (fun s ↦ ∑ i : Fin d, err s i)
    (c / (2 * Real.sqrt d)) hpoint hham
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hsqrt_sq : (Real.sqrt d) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt (le_of_lt hdR)
  convert havg using 1
  field_simp [ne_of_gt hsqrt]
  nlinarith

end

end NoisyZO
