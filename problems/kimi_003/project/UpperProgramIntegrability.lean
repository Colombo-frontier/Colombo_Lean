import UpperProgramMeasurable
import UpperOptimizationMinimizer

/-! Actual legal output gaps are measurable, integrable, nonnegative and bounded. -/

open MeasureTheory Metric

namespace Task006.Full

theorem upperProgram_output_feasible {d T : ℕ} (P : UpperProgramParameters)
    (hd : 0 < d) (hT : 0 < T) {Ω : Type*} (F : Space d → Ω → ℝ)
    (w : UpperSeed d T × (ℕ → Ω)) :
    (upperPairedProgram P hd).toAlgorithm.realizedOutput F w ∈ outputDomain d P.R :=
  (upperProgram_execution_legal P hd hT F w.2 w.1).2.2

theorem upperProgram_realizedGap_bounds {d T : ℕ} (P : UpperProgramParameters)
    (hd : 0 < d) (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L : ℝ} (hL : 0 ≤ L)
    (I : SampleInstance d L P.R Ω μ) (w : UpperSeed d T × (ℕ → Ω)) :
    0 ≤ (upperPairedProgram P hd).toAlgorithm.realizedGap I w ∧
      (upperPairedProgram P hd).toAlgorithm.realizedGap I w ≤ 2 * L * P.R := by
  have hR : 0 ≤ P.R := by linarith [P.inner_nonneg, P.rho_nonneg, P.delta_pos]
  exact I.objective_gap_bounds hL hR (upperProgram_output_feasible P hd hT I.sample w)

/-- The fixed-instance expectation in the paper is a genuine finite integral
for the actual implemented program, derived under exactly the sample model. -/
theorem upperProgram_realizedGap_integrable {d T : ℕ} (P : UpperProgramParameters)
    (hd : 0 < d) (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L : ℝ} (hL : 0 ≤ L)
    (I : SampleInstance d L P.R Ω μ) :
    Integrable ((upperPairedProgram P hd).toAlgorithm.realizedGap I)
      ((upperSeedLaw d T).prod (iidHandleLaw μ)) := by
  have hR : 0 ≤ P.R := by linarith [P.inner_nonneg, P.rho_nonneg, P.delta_pos]
  have hOut := upperProgram_output_aestronglyMeasurable (T := T) P hd I
  have hComp := (I.objectiveExtension_lipschitz hL hR).continuous.measurable.comp_aemeasurable
    hOut.aemeasurable
  have heq : (fun w => I.objectiveExtension hL hR
      ((upperPairedProgram P hd).toAlgorithm.realizedOutput I.sample w) - optimalValue I) =ᵐ[
      (upperSeedLaw d T).prod (iidHandleLaw μ)] (upperPairedProgram P hd).toAlgorithm.realizedGap I := by
    filter_upwards [] with w
    have hy := upperProgram_output_feasible P hd hT I.sample w
    have hq : (upperPairedProgram P hd).toAlgorithm.realizedOutput I.sample w ∈ queryDomain d P.R := by
      have hyn : ‖(upperPairedProgram P hd).toAlgorithm.realizedOutput I.sample w‖ ≤ P.R := by
        simpa only [outputDomain, mem_closedBall, dist_zero_right] using hy
      change dist ((upperPairedProgram P hd).toAlgorithm.realizedOutput I.sample w) 0 ≤ 2 * P.R
      rw [dist_zero_right]
      linarith
    exact congrArg (fun a => a - optimalValue I) (I.objectiveExtension_eq hL hR hq).symm
  have hMeas := (hComp.aestronglyMeasurable.sub aestronglyMeasurable_const).congr heq
  apply Integrable.of_bound hMeas (2 * L * P.R)
  filter_upwards [] with w
  have hb := upperProgram_realizedGap_bounds P hd hT hL I w
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

#print axioms upperProgram_realizedGap_integrable

end Task006.Full
