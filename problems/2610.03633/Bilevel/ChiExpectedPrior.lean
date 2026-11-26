import Bilevel.ChiExpectedLower

/-! Extended-expectation accuracy and extraction of one fixed mean
instance from a hard prior. Neither result assumes transcript coupling. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace Bilevel.ChiExpectedLower

theorem integrable_loss_of_expected_bound
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (loss : Ω → ℝ) (hml : Measurable loss) (hpos : ∀ ω,0≤loss ω) {ε : ℝ}
    (hε : 0≤ε) (hacc : (∫⁻ ω,ENNReal.ofReal (loss ω) ∂ν)≤ENNReal.ofReal ε) :
    Integrable loss ν ∧ (∫ ω,loss ω ∂ν)≤ε := by
  have hi : Integrable loss ν := by
    refine ⟨hml.aestronglyMeasurable,?_⟩
    have hf : (∫⁻ ω,ENNReal.ofReal (loss ω) ∂ν)<∞ := lt_of_le_of_lt hacc ENNReal.ofReal_lt_top
    simpa only [HasFiniteIntegral,Real.enorm_of_nonneg (hpos _)] using hf
  refine ⟨hi,?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hpos)
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp (he ▸ hacc)

theorem hard_instance_from_expected_cost
    {Frame Seed : Type*} [MeasurableSpace Frame] [MeasurableSpace Seed]
    (ν : Measure Frame) (ρ : Measure Seed) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (valid : Frame → Prop) (hvalid : ∀ᵐ I ∂ν,valid I)
    (N : Frame × Seed → ℕ) (hN : Measurable N)
    {R : ℝ} (hR : 0<R)
    (hcost : ENNReal.ofReal (R/256)≤∫⁻ ω,(N ω:ENNReal) ∂ν.prod ρ) :
    ∃ I,valid I ∧ ENNReal.ofReal (R/512)≤∫⁻ s,(N (I,s):ENNReal) ∂ρ := by
  by_contra hnone
  push_neg at hnone
  have hm : Measurable (fun ω => (N ω:ENNReal)) :=
    (measurable_of_countable (fun n : ℕ => (n:ENNReal))).comp hN
  have hbound : (∫⁻ I,∫⁻ s,(N (I,s):ENNReal) ∂ρ ∂ν)≤ENNReal.ofReal (R/512) := by
    have hh := lintegral_mono_ae (hvalid.mono (fun I hv => (hnone I hv).le))
    simpa only [lintegral_const,measure_univ,smul_eq_mul,mul_one] using hh
  rw [lintegral_prod _ hm.aemeasurable] at hcost
  have hh := (ENNReal.ofReal_le_ofReal_iff (show 0≤R/512 by positivity)).mp (hcost.trans hbound)
  linarith only [hh,hR]

end Bilevel.ChiExpectedLower
