import Bilevel.BorelAdaptiveExpectedInformation

/-! A measured fixed-horizon margin probability directly supplies the
extended original-call lower bound. Finite cost implies actual stopping;
nontermination retains infinite cost. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.BorelAdaptive
set_option autoImplicit false
variable {S Q O Y I C Private : Type*}
  [MeasurableSpace S] [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace Y]
  [MeasurableSpace I] [MeasurableSpace C] [MeasurableSpace Private]

theorem expected_seededCalls_of_fixed_probabilities
    (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial)
    (ν : Measure (Sample I Private C)) [IsProbabilityMeasure ν]
    (loss : I × Y → ℝ) (hloss : Measurable loss) (hpos : ∀ z,0≤loss z)
    (T : ℕ) (p ε : ℝ) (hp : 0<p) (hε : 0<ε)
    (hfixed : ∀ n : ℕ,(n:ℝ)≤(T:ℝ)/(16*p) →
      13/16≤ν.real {z | 8*ε≤loss (seededCapped A response initial n z)})
    (haccuracy : (∫⁻ z,ENNReal.ofReal (loss (seededStopped A response initial z)) ∂ν)≤ENNReal.ofReal ε) :
    ENNReal.ofReal ((T:ℝ)/(256*p))≤∫⁻ z,seededCalls A response initial z ∂ν := by
  by_cases hinf : (∫⁻ z,seededCalls A response initial z ∂ν)=⊤
  · rw [hinf]
    exact le_top
  have hterm := seeded_ae_terminated_of_calls_finite A response hr initial hi ν hinf
  have hml := hloss.comp (seededStopped_measurable A response hr initial hi)
  obtain ⟨hlint,hacc⟩ := ChiExpectedLower.integrable_loss_of_expected_bound ν _ hml
    (fun z => hpos _) hε.le haccuracy
  rw [seededCalls_integral_eq_time A response initial ν hterm]
  have hh := ChiExpectedLower.expected_cost_of_fixed_horizons_extended ν
    (seededTime A response initial) (seededStopped A response initial) (seededCapped A response initial)
    loss (seededTime_measurable A response hr initial hi) hlint hpos ((T:ℝ)/p) ε (by positivity) hε
    (seededAgreement_ae A response initial ν hterm) (fun n hn => ?_) hacc
  · convert hh using 1
    congr 1
    ring
  have hn' : (n:ℝ)≤(T:ℝ)/(16*p) := by convert hn using 1;ring
  refine ⟨{z | 8*ε≤loss (seededCapped A response initial n z)},
    measurableSet_le measurable_const (hloss.comp (seededCapped_measurable A response hr initial hi n)),
    hfixed n hn',?_⟩
  exact Filter.Eventually.of_forall (fun _ h => h)

end Bilevel.BorelAdaptive
