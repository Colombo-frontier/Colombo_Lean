import Bilevel.ChiExpectedPrior

/-! The source's hard-prior expected-cost interface. All actual
information events and capped/stopped loss agreement are explicit.
Uniform conditional accuracy is averaged by Tonelli, then one fixed
valid mean instance is extracted, including infinite expected costs. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace Bilevel.ChiExpectedLower

theorem expected_lower_of_information_events
    {Ω X : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (N : Ω → ℕ) (stopped : Ω → X) (capped : ℕ → Ω → X) (loss : X → ℝ)
    (hN : Measurable N) (hloss : Measurable (fun ω => loss (stopped ω))) (hpos : ∀ x,0≤loss x)
    (T : ℕ) (p ε : ℝ) (hp : 0<p) (hε : 0<ε)
    (hagreement : ∀ n,∀ᵐ ω ∂ν,N ω≤n → stopped ω=capped n ω)
    (bad activation : ℕ → Set Ω)
    (hinfo : ∀ n : ℕ,(n:ℝ)≤(T:ℝ)/(16*p) →
      MeasurableSet (bad n) ∧ MeasurableSet (activation n) ∧
      ν.real (bad n)≤1/8 ∧ ν.real (activation n)≤1/16 ∧
      (∀ᵐ ω ∂ν,ω∉bad n → ω∉activation n → 8*ε≤loss (capped n ω)))
    (haccuracy : (∫⁻ ω,ENNReal.ofReal (loss (stopped ω)) ∂ν)≤ENNReal.ofReal ε) :
    ENNReal.ofReal ((T:ℝ)/(256*p))≤∫⁻ ω,(N ω:ENNReal) ∂ν := by
  obtain ⟨hi,hacc⟩ := integrable_loss_of_expected_bound ν _ hloss (fun ω => hpos _) hε.le haccuracy
  have hh := expected_cost_of_fixed_horizons_extended ν N stopped capped loss hN hi hpos
    ((T:ℝ)/p) ε (by positivity) hε hagreement (fun n hn => ?_) hacc
  · convert hh using 1
    congr 1
    ring
  have hn' : (n:ℝ)≤(T:ℝ)/(16*p) := by convert hn using 1; ring
  obtain ⟨hb,ha,hbp,hap,hm⟩ := hinfo n hn'
  refine ⟨(bad n ∪ activation n)ᶜ,(hb.union ha).compl,
    MultiscaleRisk.good_probability ν (bad n) (activation n) hb ha hbp hap,?_⟩
  filter_upwards [hm] with ω hω
  intro hg
  exact hω (fun h => hg (Or.inl h)) (fun h => hg (Or.inr h))

theorem prior_accuracy_of_uniform
    {Frame Seed : Type*} [MeasurableSpace Frame] [MeasurableSpace Seed]
    (ν : Measure Frame) (ρ : Measure Seed) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (valid : Frame → Prop) (hvalid : ∀ᵐ I ∂ν,valid I)
    (loss : Frame × Seed → ℝ) (hloss : Measurable loss) (ε : ℝ)
    (haccuracy : ∀ I,valid I → (∫⁻ s,ENNReal.ofReal (loss (I,s)) ∂ρ)≤ENNReal.ofReal ε) :
    (∫⁻ ω,ENNReal.ofReal (loss ω) ∂ν.prod ρ)≤ENNReal.ofReal ε := by
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (loss ω)) (ν.prod ρ) :=
    (ENNReal.measurable_ofReal.comp hloss).aemeasurable
  rw [lintegral_prod _ hm]
  have hh := lintegral_mono_ae (hvalid.mono (fun I hv => haccuracy I hv))
  simpa only [lintegral_const,measure_univ,smul_eq_mul,mul_one] using hh

theorem fixed_instance_expected_queries
    {Frame Seed X : Type*} [MeasurableSpace Frame] [MeasurableSpace Seed]
    (ν : Measure Frame) (ρ : Measure Seed) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (valid : Frame → Prop) (hvalid : ∀ᵐ I ∂ν,valid I)
    (N : Frame × Seed → ℕ) (stopped : Frame × Seed → X) (capped : ℕ → Frame × Seed → X)
    (loss : X → ℝ) (hN : Measurable N)
    (hloss : Measurable (fun ω => loss (stopped ω))) (hpos : ∀ x,0≤loss x)
    (T : ℕ) (hT : 0<T) (p ε : ℝ) (hp : 0<p) (hε : 0<ε)
    (hagreement : ∀ n,∀ᵐ ω ∂ν.prod ρ,N ω≤n → stopped ω=capped n ω)
    (bad activation : ℕ → Set (Frame × Seed))
    (hinfo : ∀ n : ℕ,(n:ℝ)≤(T:ℝ)/(16*p) →
      MeasurableSet (bad n) ∧ MeasurableSet (activation n) ∧
      (ν.prod ρ).real (bad n)≤1/8 ∧ (ν.prod ρ).real (activation n)≤1/16 ∧
      (∀ᵐ ω ∂ν.prod ρ,ω∉bad n → ω∉activation n → 8*ε≤loss (capped n ω)))
    (haccuracy : ∀ I,valid I → (∫⁻ s,ENNReal.ofReal (loss (stopped (I,s))) ∂ρ)≤ENNReal.ofReal ε) :
    ∃ I,valid I ∧ ENNReal.ofReal ((T:ℝ)/(512*p))≤∫⁻ s,(N (I,s):ENNReal) ∂ρ := by
  have hacc := prior_accuracy_of_uniform ν ρ valid hvalid _ hloss ε haccuracy
  have he := expected_lower_of_information_events (ν.prod ρ) N stopped capped loss hN hloss hpos
    T p ε hp hε hagreement bad activation hinfo hacc
  have hR : 0<(T:ℝ)/p := div_pos (Nat.cast_pos.mpr hT) hp
  have hc : ENNReal.ofReal (((T:ℝ)/p)/256)≤∫⁻ ω,(N ω:ENNReal) ∂ν.prod ρ := by
    convert he using 1
    congr 1
    ring
  obtain ⟨I,hI,hcost⟩ := hard_instance_from_expected_cost ν ρ valid hvalid N hN hR hc
  refine ⟨I,hI,?_⟩
  convert hcost using 1
  congr 1
  ring

end Bilevel.ChiExpectedLower
