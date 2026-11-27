import HaarRebalancingCutoff
open MeasureTheory MeasureTheory.Measure Set Function
namespace Task006.SphereConcentration

/-- The literal any-median Markov bound used in the source, including the
lower bound from a nonnegative random variable. -/
theorem median_bound_of_threeHalves_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {a : Ω → ℝ} (ha : Measurable a)
    (hpos : ∀ᵐ ω ∂μ, 0 ≤ a ω) {M m : ℝ} (hM : 0 ≤ M)
    (hi : Integrable (fun ω => a ω^(3/2:ℝ)) μ)
    (hbudget : (∫ ω, a ω^(3/2:ℝ) ∂μ) ≤ M)
    (hlo : (1/2:ℝ) ≤ μ.real {ω | a ω ≤ m})
    (hhi : (1/2:ℝ) ≤ μ.real {ω | m ≤ a ω}) :
    0 ≤ m ∧ m ≤ (2*M)^(2/3:ℝ) := by
  have hm : 0 ≤ m := by
    by_contra h
    have hn : m < 0 := lt_of_not_ge h
    have hz : ∀ᵐ ω ∂μ, ¬(a ω ≤ m) := by
      filter_upwards [hpos] with ω hω
      linarith
    have hzero := ae_iff.1 hz
    simp only [not_not] at hzero
    have hr : μ.real {ω | a ω ≤ m}=0 := by rw [measureReal_def,hzero,ENNReal.toReal_zero]
    linarith
  have hA : MeasurableSet {ω | m ≤ a ω} := measurableSet_le measurable_const ha
  have hI := (integrable_const (m^(3/2:ℝ)) (μ := μ)).indicator hA
  have hdom : ∀ᵐ ω ∂μ, {ω | m ≤ a ω}.indicator (fun _ => m^(3/2:ℝ)) ω ≤ a ω^(3/2:ℝ) := by
    filter_upwards [hpos] with ω hω
    by_cases h : m ≤ a ω
    · have hmemb : ω ∈ {v | m ≤ a v} := h
      rw [indicator_of_mem hmemb]
      exact Real.rpow_le_rpow hm h (by norm_num)
    · have hnot : ω ∉ {v | m ≤ a v} := h
      rw [indicator_of_notMem hnot]
      exact Real.rpow_nonneg hω _
  have hmono := integral_mono_ae hI hi hdom
  rw [integral_indicator_const _ hA,smul_eq_mul] at hmono
  have hpow : m^(3/2:ℝ) ≤ 2*M := by
    have hh := mul_le_mul_of_nonneg_right hhi (Real.rpow_nonneg hm (3/2:ℝ))
    nlinarith
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg hm (3/2:ℝ)) hpow (by norm_num : (0:ℝ) ≤ 2/3)
  rw [← Real.rpow_mul hm,show (3/2:ℝ)*(2/3:ℝ)=1 by norm_num,Real.rpow_one] at hr
  exact ⟨hm,hr⟩

/-- Explicit B_r*L/sqrt(d) form after the actual U5 moment estimate. -/
theorem median_bound_spherical_scale {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {a : Ω → ℝ} (ha : Measurable a)
    (hpos : ∀ᵐ ω ∂μ, 0 ≤ a ω) {C L d m : ℝ} (hC : 0 ≤ C) (hL : 0 < L) (hd : 0 < d)
    (hi : Integrable (fun ω => a ω^(3/2:ℝ)) μ)
    (hb : (∫ ω, a ω^(3/2:ℝ) ∂μ) ≤ C*L^(3/2:ℝ)/d^(3/4:ℝ))
    (hlo : (1/2:ℝ) ≤ μ.real {ω | a ω ≤ m})
    (hhi : (1/2:ℝ) ≤ μ.real {ω | m ≤ a ω}) :
    0 ≤ m ∧ m ≤ (2*C)^(2/3:ℝ)*L/Real.sqrt d := by
  have hh := median_bound_of_threeHalves_moment ha hpos
    (show 0 ≤ C*L^(3/2:ℝ)/d^(3/4:ℝ) by positivity) hi hb hlo hhi
  rw [Task006.HaarRebalancing.thirdHalf_markov_cutoff hC hL hd] at hh
  exact hh

end Task006.SphereConcentration
