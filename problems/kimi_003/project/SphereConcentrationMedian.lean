import SLT.GaussianLipConcen
import Mathlib.Probability.ConditionalProbability

/-!
A Gaussian concentration-to-conditioned-median transfer, with explicit universal
constants. The concentration input is the proved, compiled SLT theorem. The
conditioning event only needs probability at least 1/16. No spherical
concentration assertion is assumed.
-/

open Set MeasureTheory ProbabilityTheory GaussianMeasure
open scoped ENNReal NNReal ProbabilityTheory

namespace Task006.SphereConcentration
noncomputable section

/-- Conditional probabilities multiplied by their actual event mass recover
intersection mass, including their real-valued versions. -/
theorem cond_real_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet A) (B : Set Ω) :
    (μ[|A]).real B * μ.real A = μ.real (A ∩ B) := by
  have h := congrArg ENNReal.toReal (cond_mul_eq_inter hA B μ)
  simpa only [Measure.real, ENNReal.toReal_mul] using h

/-- A half-mass event after conditioning has unconditional mass at least
1/32 whenever the conditioning event has mass at least 1/16. -/
theorem conditioned_half_mass_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A B : Set Ω} (hA : MeasurableSet A)
    (hmass : (1 / 16 : ℝ) ≤ μ.real A)
    (hhalf : (1 / 2 : ℝ) ≤ (μ[|A]).real B) :
    (1 / 32 : ℝ) ≤ μ.real B := by
  have hm := cond_real_mul μ hA B
  have hmono : μ.real (A ∩ B) ≤ μ.real B := measureReal_mono inter_subset_right
  have hprod := mul_le_mul hhalf hmass (by norm_num : (0 : ℝ) ≤ 1 / 16)
    (measureReal_nonneg (μ := μ[|A]) (s := B))
  nlinarith only [hm, hmono, hprod]

/-- Elementary exponential arithmetic needed for the explicit median shift. -/
theorem exp_neg_thirtyTwo_lt : Real.exp (-32 : ℝ) < (1 / 32 : ℝ) := by
  have h : (32 : ℝ) < Real.exp 32 := by
    have he := Real.add_one_le_exp (32 : ℝ)
    linarith
  rw [Real.exp_neg, one_div]
  exact (inv_lt_inv₀ (Real.exp_pos _) (by norm_num)).2 h

/-- If zero is a lower median after conditioning, the Gaussian mean cannot
lie more than eight Lipschitz constants above zero. -/
theorem gaussian_mean_le_of_conditioned_lower_median {n : ℕ} (hn : 0 < n)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hK : 0 < K) (hg : LipschitzWith K g)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hmass : (1 / 16 : ℝ) ≤ (stdGaussianE n).real A)
    (hmedian : (1 / 2 : ℝ) ≤ ((stdGaussianE n)[|A]).real {x | g x ≤ 0}) :
    (∫ x, g x ∂stdGaussianE n) ≤ 8 * (K : ℝ) := by
  by_contra hnot
  have hmean : 8 * (K : ℝ) < ∫ x, g x ∂stdGaussianE n := lt_of_not_ge hnot
  have hKreal : 0 < (K : ℝ) := hK
  have hsub : {x | g x ≤ 0} ⊆
      {x | 8 * (K : ℝ) ≤ -g x - ∫ y, -g y ∂stdGaussianE n} := by
    intro x hx
    rw [integral_neg]
    change g x ≤ 0 at hx
    dsimp only [mem_setOf_eq]
    linarith
  have hlower := conditioned_half_mass_lower (stdGaussianE n) hA hmass hmedian
  have htail := GaussianLipConcen.gaussian_lipschitz_concentration_one_sided
    hn hK hg.neg (8 * (K : ℝ)) (by positivity)
  have halg : -(8 * (K : ℝ)) ^ 2 / (2 * (K : ℝ) ^ 2) = (-32 : ℝ) := by
    field_simp [hKreal.ne'] <;> ring
  rw [halg] at htail
  have hbound := (measureReal_mono (μ := stdGaussianE n) hsub).trans htail
  exact (not_le_of_gt exp_neg_thirtyTwo_lt) (hlower.trans hbound)

/-- A genuine two-sided conditioned median controls the Gaussian mean. -/
theorem abs_gaussian_mean_le_of_conditioned_median {n : ℕ} (hn : 0 < n)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hK : 0 < K) (hg : LipschitzWith K g)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hmass : (1 / 16 : ℝ) ≤ (stdGaussianE n).real A)
    (hlo : (1 / 2 : ℝ) ≤ ((stdGaussianE n)[|A]).real {x | g x ≤ 0})
    (hhi : (1 / 2 : ℝ) ≤ ((stdGaussianE n)[|A]).real {x | 0 ≤ g x}) :
    |∫ x, g x ∂stdGaussianE n| ≤ 8 * (K : ℝ) := by
  apply abs_le.mpr
  constructor
  · have hneg : (1 / 2 : ℝ) ≤ ((stdGaussianE n)[|A]).real {x | -g x ≤ 0} := by
      simpa only [neg_nonpos] using hhi
    have h := gaussian_mean_le_of_conditioned_lower_median hn hK hg.neg hA hmass hneg
    simp only [Pi.neg_apply, integral_neg] at h
    linarith
  · exact gaussian_mean_le_of_conditioned_lower_median hn hK hg hA hmass hlo

/-- The conditioned law inherits an explicit Gaussian-type tail around its
median; its universal prefactor absorbs both conditioning and mean shift. -/
theorem gaussian_conditioned_median_concentration {n : ℕ} (hn : 0 < n)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ≥0}
    (hK : 0 < K) (hg : LipschitzWith K g)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hmass : (1 / 16 : ℝ) ≤ (stdGaussianE n).real A)
    (hlo : (1 / 2 : ℝ) ≤ ((stdGaussianE n)[|A]).real {x | g x ≤ 0})
    (hhi : (1 / 2 : ℝ) ≤ ((stdGaussianE n)[|A]).real {x | 0 ≤ g x})
    {t : ℝ} (ht : 0 < t) :
    ((stdGaussianE n)[|A]).real {x | t ≤ |g x|} ≤
      Real.exp 128 * Real.exp (-t ^ 2 / (8 * (K : ℝ) ^ 2)) := by
  have hKreal : 0 < (K : ℝ) := hK
  have hKsq : 0 < (K : ℝ) ^ 2 := sq_pos_of_pos hKreal
  have hAne : stdGaussianE n A ≠ 0 := by
    intro hz
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hmass
    norm_num at hmass
  letI : IsProbabilityMeasure ((stdGaussianE n)[|A]) := cond_isProbabilityMeasure hAne
  have hmean := abs_gaussian_mean_le_of_conditioned_median hn hK hg hA hmass hlo hhi
  by_cases hlarge : 16 * (K : ℝ) ≤ t
  · have hsub : A ∩ {x | t ≤ |g x|} ⊆
        {x | t / 2 ≤ |g x - ∫ y, g y ∂stdGaussianE n|} := by
      intro x hx
      have htri := abs_add_le (g x - ∫ y, g y ∂stdGaussianE n)
        (∫ y, g y ∂stdGaussianE n)
      rw [sub_add_cancel] at htri
      have hxg := hx.2
      change t ≤ |g x| at hxg
      dsimp only [mem_setOf_eq]
      linarith only [hxg, htri, hmean, hlarge]
    have htail := GaussianLipConcen.gaussian_lipschitz_concentration hn hK hg
      (t / 2) (by positivity)
    have halg : -(t / 2) ^ 2 / (2 * (K : ℝ) ^ 2) = -t ^ 2 / (8 * (K : ℝ) ^ 2) := by
      ring
    rw [halg] at htail
    have hprod := cond_real_mul (stdGaussianE n) hA {x | t ≤ |g x|}
    have hi := (measureReal_mono (μ := stdGaussianE n) hsub).trans htail
    have hqnonneg : 0 ≤ ((stdGaussianE n)[|A]).real {x | t ≤ |g x|} := measureReal_nonneg
    have hscale := mul_le_mul_of_nonneg_left hmass hqnonneg
    have h32 : ((stdGaussianE n)[|A]).real {x | t ≤ |g x|} ≤
        32 * Real.exp (-t ^ 2 / (8 * (K : ℝ) ^ 2)) := by
      nlinarith only [hprod, hi, hscale]
    have hconstant : (32 : ℝ) ≤ Real.exp 128 := by
      have h := Real.add_one_le_exp (128 : ℝ)
      linarith
    exact h32.trans (mul_le_mul_of_nonneg_right hconstant (Real.exp_pos _).le)
  · have htupper : t < 16 * (K : ℝ) := lt_of_not_ge hlarge
    have hexponent : t ^ 2 / (8 * (K : ℝ) ^ 2) ≤ 32 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (K : ℝ) ^ 2)).2
      nlinarith [sq_nonneg (16 * (K : ℝ) - t)]
    have hexp : 1 ≤ Real.exp (128 + (-t ^ 2 / (8 * (K : ℝ) ^ 2))) := by
      apply Real.one_le_exp
      rw [neg_div]
      linarith only [hexponent]
    have hbound : 1 ≤ Real.exp 128 * Real.exp (-t ^ 2 / (8 * (K : ℝ) ^ 2)) := by
      rwa [Real.exp_add] at hexp
    exact (measureReal_le_one (μ := (stdGaussianE n)[|A])).trans hbound

end
end Task006.SphereConcentration
