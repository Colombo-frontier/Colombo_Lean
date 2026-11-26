import SampleReuse.PersistentStageFastProbability
import SampleReuse.SlowDimension

/-! The manuscript's concrete slow scale discharges every information,
horizon, integer-quota, and positive-stage hypothesis. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section

theorem SlowCalibratedConditions.radius_two {P : Parameters} {ε : ℝ}
    (hc : SlowCalibratedConditions P ε) : 2 ≤ slowCoefficientRadius P ε := by
  linarith [hc.radius_large]

theorem SlowCalibratedConditions.links_pos {P : Parameters} {ε : ℝ}
    (hc : SlowCalibratedConditions P ε) : 0 < slowLinks P ε :=
  (firstOrderBudgetLinks_lower
    (slowAmplitude_pos (slowBlockSize_pos P hc.tolerance_pos) hc.tolerance_pos)
    hc.amplitude_small).1

theorem SlowCalibratedConditions.responseCap_pos {P : Parameters} {ε : ℝ}
    (hc : SlowCalibratedConditions P ε) : 0 < firstOrderResponseCap (slowCoefficientRadius P ε) := by
  have hr := hc.radius_large
  exact (firstOrderResponseCap_bounds (by nlinarith : 32768 ≤ (slowCoefficientRadius P ε)^2)).1

/-- No per-stage probability premise remains: this is the actual immutable
table law at the calibrated manuscript parameters. -/
theorem slow_calibrated_stage_fast {H S : Type} [Fintype H]
    (P : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions P ε)
    (policy : PersistentFirstOrderPolicy (slowBlockSize P ε) (slowLinks P ε) H S)
    (N : ℕ) (hN : (N : ℝ) ≤ slowQueryThreshold P ε) (i : Fin (slowLinks P ε)) :
    pmfEventProbability
      (persistentSourceLaw (slowBlockSize P ε) (slowLinks P ε) H (slowCoefficientRadius P ε) hc.radius_two)
      (fun w => decide (persistentFastOutcome policy (slowAmplitude (slowBlockSize P ε) ε)
        (slowDilation (slowBlockSize P ε)) i.succ (firstOrderResponseCap (slowCoefficientRadius P ε)) N w)) ≤
      1 / 32 := by
  have hh := slow_calibrated_stage_scalars P hc N hN
  exact persistent_stage_fast_probability policy (slowAmplitude (slowBlockSize P ε) ε)
    (slowDilation (slowBlockSize P ε)) (slowCoefficientRadius P ε) hc.radius_two i.succ (Nat.zero_lt_succ _)
    N (firstOrderResponseCap (slowCoefficientRadius P ε)) (fun _ => Classical.choice inferInstance)
    hh.1 hh.2.1 hh.2.2

end
end SampleReuse
