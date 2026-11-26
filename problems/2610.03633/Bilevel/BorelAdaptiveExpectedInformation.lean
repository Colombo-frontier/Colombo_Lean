import Bilevel.BorelAdaptiveExtendedCalls
import Bilevel.ChiExpectedInformationBridge

/-! Fixed-horizon information bounds imply an expected lower bound for
the actual original program. Nontermination costs infinity, so neither
almost-sure termination nor an integrable stopping time is assumed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.BorelAdaptive

variable {S Q O Y I C Private : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSpace C]
  [MeasurableSpace Private]

theorem expected_seededCalls_of_information_events
    (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial)
    (ν : Measure (Sample I Private C)) [IsProbabilityMeasure ν]
    (loss : I × Y → ℝ) (hloss : Measurable (fun z => loss (seededStopped A response initial z)))
    (hpos : ∀ z,0≤loss z) (T : ℕ) (p ε : ℝ) (hp : 0<p) (hε : 0<ε)
    (bad activation : ℕ → Set (Sample I Private C))
    (hinfo : ∀ n : ℕ,(n:ℝ)≤(T:ℝ)/(16*p) →
      MeasurableSet (bad n) ∧ MeasurableSet (activation n) ∧
      ν.real (bad n)≤1/8 ∧ ν.real (activation n)≤1/16 ∧
      (∀ᵐ z ∂ν,z∉bad n → z∉activation n → 8*ε≤loss (seededCapped A response initial n z)))
    (haccuracy : (∫⁻ z,ENNReal.ofReal (loss (seededStopped A response initial z)) ∂ν)≤ENNReal.ofReal ε) :
    ENNReal.ofReal ((T:ℝ)/(256*p))≤∫⁻ z,seededCalls A response initial z ∂ν := by
  by_cases hinf : (∫⁻ z,seededCalls A response initial z ∂ν)=⊤
  · rw [hinf]
    exact le_top
  have hterm := seeded_ae_terminated_of_calls_finite A response hr initial hi ν hinf
  rw [seededCalls_integral_eq_time A response initial ν hterm]
  exact ChiExpectedLower.expected_lower_of_information_events ν
    (seededTime A response initial) (seededStopped A response initial) (seededCapped A response initial)
    loss (seededTime_measurable A response hr initial hi) hloss hpos T p ε hp hε
    (seededAgreement_ae A response initial ν hterm) bad activation hinfo haccuracy

theorem fixed_instance_of_extended_expected_cost
    {Frame Seed : Type*} [MeasurableSpace Frame] [MeasurableSpace Seed]
    (ν : Measure Frame) (ρ : Measure Seed) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (valid : Frame → Prop) (hvalid : ∀ᵐ a ∂ν,valid a)
    (cost : Frame × Seed → ℝ≥0∞) (hc : Measurable cost) {R : ℝ} (hR : 0<R)
    (hcost : ENNReal.ofReal (R/256)≤∫⁻ z,cost z ∂ν.prod ρ) :
    ∃ a,valid a ∧ ENNReal.ofReal (R/512)≤∫⁻ s,cost (a,s) ∂ρ := by
  by_contra hnone
  push_neg at hnone
  have hb : (∫⁻ a,∫⁻ s,cost (a,s) ∂ρ ∂ν)≤ENNReal.ofReal (R/512) := by
    have hh := lintegral_mono_ae (hvalid.mono (fun a ha => (hnone a ha).le))
    simpa only [lintegral_const,measure_univ,smul_eq_mul,mul_one] using hh
  rw [lintegral_prod _ hc.aemeasurable] at hcost
  have hh := (ENNReal.ofReal_le_ofReal_iff (show 0≤R/512 by positivity)).mp (hcost.trans hb)
  linarith

theorem fixed_instance_expected_seededCalls
    (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial)
    (ν : Measure I) (ρ : Measure (Private × (ℕ → C))) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (valid : I → Prop) (hvalid : ∀ᵐ a ∂ν,valid a)
    (loss : I × Y → ℝ) (hloss : Measurable (fun z => loss (seededStopped A response initial z)))
    (hpos : ∀ z,0≤loss z) (T : ℕ) (hT : 0<T) (p ε : ℝ) (hp : 0<p) (hε : 0<ε)
    (bad activation : ℕ → Set (Sample I Private C))
    (hinfo : ∀ n : ℕ,(n:ℝ)≤(T:ℝ)/(16*p) →
      MeasurableSet (bad n) ∧ MeasurableSet (activation n) ∧
      (ν.prod ρ).real (bad n)≤1/8 ∧ (ν.prod ρ).real (activation n)≤1/16 ∧
      (∀ᵐ z ∂ν.prod ρ,z∉bad n → z∉activation n → 8*ε≤loss (seededCapped A response initial n z)))
    (haccuracy : ∀ a,valid a →
      (∫⁻ s,ENNReal.ofReal (loss (seededStopped A response initial (a,s))) ∂ρ)≤ENNReal.ofReal ε) :
    ∃ a,valid a ∧ ENNReal.ofReal ((T:ℝ)/(512*p))≤∫⁻ s,seededCalls A response initial (a,s) ∂ρ := by
  have hacc := ChiExpectedLower.prior_accuracy_of_uniform ν ρ valid hvalid _ hloss ε haccuracy
  have hc := expected_seededCalls_of_information_events A response hr initial hi (ν.prod ρ)
    loss hloss hpos T p ε hp hε bad activation hinfo hacc
  have hR : 0<(T:ℝ)/p := div_pos (Nat.cast_pos.mpr hT) hp
  have hc' : ENNReal.ofReal (((T:ℝ)/p)/256)≤∫⁻ z,seededCalls A response initial z ∂ν.prod ρ := by
    convert hc using 1
    congr 1
    ring
  obtain ⟨a,ha,ha'⟩ := fixed_instance_of_extended_expected_cost ν ρ valid hvalid
    (seededCalls A response initial) (seededCalls_measurable A response hr initial hi) hR hc'
  refine ⟨a,ha,?_⟩
  convert ha' using 1
  congr 1
  ring

end Bilevel.BorelAdaptive
