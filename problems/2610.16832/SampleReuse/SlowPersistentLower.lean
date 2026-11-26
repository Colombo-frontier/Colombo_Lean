import SampleReuse.SlowPersistentFast
import SampleReuse.PersistentExpectedLower

open SecondOrder MeasureTheory
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section

theorem slow_calibrated_completion {H S : Type} [Fintype H]
    (M : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions M ε)
    (P : PersistentFirstOrderPolicy (slowBlockSize M ε) (slowLinks M ε) H S)
    (N : ℕ) (hN : (N:ℝ) ≤ slowQueryThreshold M ε) :
    pmfEventProbability (persistentSourceLaw (slowBlockSize M ε) (slowLinks M ε) H
      (slowCoefficientRadius M ε) hc.radius_two) (fun w => decide
      (persistentOutputProgress P (persistentSourceHidden w) (slowAmplitude (slowBlockSize M ε) ε)
        (slowDilation (slowBlockSize M ε)) (persistentSourceTable w) N = slowLinks M ε+1)) ≤ 1/16 := by
  apply persistent_completion_probability P hc.links_pos _ _ _ hc.radius_two _ N
    hc.responseCap_pos (slow_query_nat_budget M hc N hN)
  intro i
  simpa only [pmfEventProbability_mean,decide_eq_true_eq,persistentFastOutcome,persistentStageReached,Fin.val_succ] using
    slow_calibrated_stage_fast M hc P N hN i

theorem slow_calibrated_gradient_complete (M : Parameters) {ε : ℝ}
    (hc : SlowCalibratedConditions M ε)
    (Θ : Fin (slowLinks M ε+1) → Fin (slowBlockSize M ε) → Bool)
    (x : Point (FirstOrderDimension (slowBlockSize M ε) (slowLinks M ε)))
    (hx : ‖gradient (scaledFirstOrderPopulation Θ (slowAmplitude (slowBlockSize M ε) ε)
      (slowDilation (slowBlockSize M ε))) x‖ ≤ ε) :
    firstOrderProgress Θ (firstOrderDilation (slowBlockSize M ε) (slowLinks M ε)
      (slowDilation (slowBlockSize M ε)) x) = slowLinks M ε+1 := by
  have hd := slowBlockSize_pos M hc.tolerance_pos
  apply scaledFirstOrderPopulation_gradient_progress Θ hd
    (slowAmplitude_pos hd hc.tolerance_pos).le (inv_nonneg.mpr (slowAlpha_pos hd).le) _ hx
  change ε < slowAmplitude (slowBlockSize M ε) ε * slowDilation (slowBlockSize M ε) * firstOrderGradientConstant
  rw [slowAmplitude_scale hd]
  linarith [hc.tolerance_pos]

theorem slow_calibrated_gradient_one_eighth {H S : Type} [Fintype H]
    (M : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions M ε)
    (P : PersistentFirstOrderPolicy (slowBlockSize M ε) (slowLinks M ε) H S)
    (N : ℕ) (hN : (N:ℝ) ≤ slowQueryThreshold M ε) :
    pmfEventProbability (persistentSourceLaw (slowBlockSize M ε) (slowLinks M ε) H
      (slowCoefficientRadius M ε) hc.radius_two) (fun w => decide
      (‖gradient (scaledFirstOrderPopulation (persistentSourceHidden w)
        (slowAmplitude (slowBlockSize M ε) ε) (slowDilation (slowBlockSize M ε)))
        (persistentOriginalOutput P (persistentSourceHidden w) (slowAmplitude (slowBlockSize M ε) ε)
          (slowDilation (slowBlockSize M ε)) (persistentSourceTable w) N)‖ ≤ ε)) ≤ 1/8 := by
  apply persistent_original_success_one_eighth P hc.links_pos _ _ _ hc.radius_two _ N
    hc.responseCap_pos (slow_query_nat_budget M hc N hN) _
    (slow_calibrated_horizon M hc N hN).2.2 _ (slow_calibrated_gradient_complete M hc)
  intro i
  simpa only [pmfEventProbability_mean,decide_eq_true_eq,persistentFastOutcome,persistentStageReached,Fin.val_succ] using
    slow_calibrated_stage_fast M hc P N hN i

def slowPopulation (M : Parameters) (ε : ℝ)
    (Θ : Fin (slowLinks M ε+1) → Fin (slowBlockSize M ε) → Bool) :=
  scaledFirstOrderPopulation Θ (slowAmplitude (slowBlockSize M ε) ε) (slowDilation (slowBlockSize M ε))

def slowSample (M : Parameters) (ε : ℝ)
    (Θ : Fin (slowLinks M ε+1) → Fin (slowBlockSize M ε) → Bool) :=
  scaledFirstOrderSample (R := slowCoefficientRadius M ε) Θ
    (slowAmplitude (slowBlockSize M ε) ε) (slowDilation (slowBlockSize M ε))

def slowLaw (M : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions M ε)
    (Θ : Fin (slowLinks M ε+1) → Fin (slowBlockSize M ε) → Bool) :=
  firstOrderChainCoefficientLaw Θ (slowCoefficientRadius M ε) hc.radius_two

def slowReply (M : Parameters) (ε : ℝ)
    (Θ : Fin (slowLinks M ε+1) → Fin (slowBlockSize M ε) → Bool)
    (x : Point (FirstOrderDimension (slowBlockSize M ε) (slowLinks M ε)))
    (z : FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)) :=
  richReply (slowSample M ε Θ) z x

theorem slow_calibrated_expected_lower {H S Ξ : Type} [MeasurableSpace Ξ]
    (M : Parameters) {ε : ℝ} (hc : SlowCalibratedConditions M ε)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → FirstOrderStoppingAlgorithm (slowBlockSize M ε) (slowLinks M ε) H S)
    (N : ℕ) (hN : (N:ℝ) ≤ slowQueryThreshold M ε)
    (hE : ∀ Θ (table : Fin (N+1) → FirstOrderCoefficients (slowBlockSize M ε)
      (slowLinks M ε) (slowCoefficientRadius M ε)), MeasurableSet {ξ |
        ‖gradient (slowPopulation M ε Θ) (persistentOriginalOutput (firstOrderStoppingCapPolicy (P ξ) N)
          Θ (slowAmplitude (slowBlockSize M ε) ε) (slowDilation (slowBlockSize M ε)) table N)‖ ≤ ε})
    (hs : ∀ Θ n, Measurable (fun w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε)
      (slowLinks M ε) (slowCoefficientRadius M ε)) => (P w.1).stopOnRun (slowReply M ε Θ) w.2 n))
    (hsolve : ∀ Θ, (2/3:ℝ) ≤ (μ.prod (iidSampleTapeLaw (slowLaw M hc Θ))).real
      {w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)) |
        (P w.1).Halts (slowReply M ε Θ) w.2 ∧
        ‖gradient (slowPopulation M ε Θ) ((P w.1).outputFor (slowReply M ε Θ) w.2)‖ ≤ ε}) :
    ∃ Θ, Admissible (slowLaw M hc Θ).toMeasure M (slowPopulation M ε Θ) (slowSample M ε Θ) 0 ∧
      (N+1:ℕ) * ENNReal.ofReal (5/12) ≤
        ∫⁻ w : Ξ × (ℕ → FirstOrderCoefficients (slowBlockSize M ε) (slowLinks M ε) (slowCoefficientRadius M ε)),
          (P w.1).extendedCost (slowReply M ε Θ) w.2 ∂μ.prod (iidSampleTapeLaw (slowLaw M hc Θ)) := by
  obtain ⟨Θ,hΘ⟩ := persistent_stopping_expected_lower μ P hc.links_pos
    (slowAmplitude (slowBlockSize M ε) ε) (slowDilation (slowBlockSize M ε))
    (slowCoefficientRadius M ε) hc.radius_two _ N hc.responseCap_pos
    (slow_query_nat_budget M hc N hN)
    (fun ξ i => by simpa only [pmfEventProbability_mean,decide_eq_true_eq,persistentFastOutcome,persistentStageReached,Fin.val_succ] using
      slow_calibrated_stage_fast M hc (firstOrderStoppingCapPolicy (P ξ) N) N hN i)
    (slow_calibrated_horizon M hc N hN).2.2
    (fun Θ x => ‖gradient (slowPopulation M ε Θ) x‖ ≤ ε)
    (slow_calibrated_gradient_complete M hc) hE hs hsolve
  exact ⟨Θ,calibrated_slow_sample_admissible M hc Θ,hΘ⟩

end
end SampleReuse
