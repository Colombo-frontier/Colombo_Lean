import SecondOrder.OjaAmplifiedCost
import SecondOrder.TrackingParameters

open MeasureTheory
open scoped ENNReal

namespace SecondOrder
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- Instantiate the finite optimizer with the actual amplified HVP routine
and its complete deterministic query count. The curvature correctness
contract is proved from CommonLoss, not supplied as an additional input.
The asymptotic simplification of this price is a separate remaining step. -/
theorem CommonLoss.selectedOjaBudgetedRun_success (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) :
    let M := physicalCap P ν (ε/10) γ
    let δ := localFailureTolerance M
    let κ := ojaAmplifiedQueryCount P d γ δ
    ENNReal.ofReal (29/32:ℝ) ≤
      ((finiteTrackingLaw μ (ojaAmplifiedLaw μ P hd hγ δ) P (trackingTreeDepth M) (ε/10) δ M).prod
        (signLaw M)) {w | BudgetedSuccess F ε γ
          (selectedBudgetedRun P ν (ε/10) γ κ f (fun x => ojaAmplifiedReply P f x γ δ) w)} := by
  let M := physicalCap P ν (ε/10) γ
  let δ := localFailureTolerance M
  let κ := ojaAmplifiedQueryCount P d γ δ
  let routine : Point d → OjaAmplifiedDraws Ω d P γ δ → CurvatureReply d :=
    fun x => ojaAmplifiedReply P f x γ δ
  have hm : Measurable (fun w : Point d × OjaAmplifiedDraws Ω d P γ δ => routine w.1 w.2) :=
    h.ojaAmplifiedReply_measurable γ δ
  have hc : ∀ x, ojaAmplifiedLaw μ P hd hγ δ
      {w | ¬ ValidCurvatureReply F γ x (routine x w)} ≤ ENNReal.ofReal δ := by
    intro x
    simp_rw [validCurvatureReply_iff_rayleigh]
    exact h.ojaAmplifiedReply_confidence hd hγ (localFailureTolerance_pos M) (localFailureTolerance_le_one M) x
  exact h.selectedBudgetedRun_epsilon_success (η := ojaAmplifiedLaw μ P hd hγ δ)
    (routine := routine) hε hγ hm hc κ

end
end SecondOrder
