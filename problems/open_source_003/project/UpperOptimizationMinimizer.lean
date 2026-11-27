import UpperSmoothingInstance
import OracleSemantics

/-! Existence of the manuscript's constrained minimizer and legal gap bounds. -/

open MeasureTheory Set Metric

namespace Task006.Full.SampleInstance

variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : Task006.Full.SampleInstance d L R Ω μ)

theorem objective_continuousOn_output (hL : 0 ≤ L) (hR : 0 ≤ R) :
    ContinuousOn I.objective (Task006.Full.outputDomain d R) := by
  apply (I.objective_lipschitzOn hL hR).continuousOn.mono
  exact closedBall_subset_closedBall (by linarith)

theorem exists_objective_minimizer (hL : 0 ≤ L) (hR : 0 ≤ R) :
    ∃ x ∈ Task006.Full.outputDomain d R,
      I.objective x = Task006.Full.optimalValue I ∧
        ∀ y ∈ Task006.Full.outputDomain d R, I.objective x ≤ I.objective y := by
  have hne : (Task006.Full.outputDomain d R).Nonempty := ⟨0, by simpa [Task006.Full.outputDomain] using hR⟩
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall (0 : Task006.Full.Space d) R).exists_isMinOn hne
    (I.objective_continuousOn_output hL hR)
  have hsetne : (I.objective '' Task006.Full.outputDomain d R).Nonempty := hne.image I.objective
  have hbounded : BddBelow (I.objective '' Task006.Full.outputDomain d R) := by
    refine ⟨I.objective x, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy
  have hInf : Task006.Full.optimalValue I = I.objective x := by
    unfold Task006.Full.optimalValue
    apply le_antisymm (csInf_le hbounded ⟨x, hx, rfl⟩)
    apply le_csInf hsetne
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy
  exact ⟨x, hx, hInf.symm, fun y hy => hmin hy⟩

theorem objective_gap_bounds (hL : 0 ≤ L) (hR : 0 ≤ R)
    {y : Task006.Full.Space d} (hy : y ∈ Task006.Full.outputDomain d R) :
    0 ≤ I.objective y - Task006.Full.optimalValue I ∧
      I.objective y - Task006.Full.optimalValue I ≤ 2 * L * R := by
  obtain ⟨x, hx, hval, hmin⟩ := I.exists_objective_minimizer hL hR
  have hxn : ‖x‖ ≤ R := by simpa only [Task006.Full.outputDomain, mem_closedBall, dist_zero_right] using hx
  have hyn : ‖y‖ ≤ R := by simpa only [Task006.Full.outputDomain, mem_closedBall, dist_zero_right] using hy
  have hxq : x ∈ Task006.Full.queryDomain d R := by
    change dist x 0 ≤ 2 * R
    rw [dist_zero_right]
    linarith
  have hyq : y ∈ Task006.Full.queryDomain d R := by
    change dist y 0 ≤ 2 * R
    rw [dist_zero_right]
    linarith
  have hdist : ‖y - x‖ ≤ 2 * R := by linarith [norm_sub_le y x]
  have hgap := (le_abs_self (I.objective y - I.objective x)).trans
    ((I.objective_lipschitz hL hR hyq hxq).trans (mul_le_mul_of_nonneg_left hdist hL))
  constructor
  · rw [← hval]
    exact sub_nonneg.mpr (hmin y hy)
  · rw [← hval]
    nlinarith

#print axioms exists_objective_minimizer
#print axioms objective_gap_bounds

end Task006.Full.SampleInstance
