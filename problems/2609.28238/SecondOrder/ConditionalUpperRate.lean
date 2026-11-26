import SecondOrder.PolylogQueryCap

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {d : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure Ψ} [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The rate is attached to the actual selected sampler, not merely to
an algebraic proxy: its recorded price obeys the bound on every path and
its actual successful output is an (ε,γ)-SOSP with probability ≥29/32.

This is deliberately conditional on a supplied curvature routine's
measurability, confidence and displayed price bound. It does not prove
that a gradient/HVP eigensolver with those properties exists, nor that
its actual oracle calls are counted by κ. -/
theorem CommonLoss.selectedBudgetedRun_conditional_rate (h : CommonLoss μ P ν F f)
    {ε γ E : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hE : 0 ≤ E)
    {κ : ℕ} (hκ : (κ : ℝ) ≤ E*(toleranceLog ε γ)^4/γ^2)
    {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤
      ENNReal.ofReal (localFailureTolerance (physicalCap P ν (ε/10) γ))) :
    let M := physicalCap P ν (ε/10) γ
    (∀ w : FiniteTrackingTape Ω Ψ P (trackingTreeDepth M) (ε/10) (localFailureTolerance M) M × (Fin M → Bool),
      ((selectedBudgetedRun P ν (ε/10) γ κ f routine w).2.1 : ℝ) <
        epsilonQueryCoefficient P ν E*(toleranceLog ε γ)^4*holderEndpointRate ν ε γ) ∧
    ENNReal.ofReal (29/32 : ℝ) ≤
      ((finiteTrackingLaw μ η P (trackingTreeDepth M) (ε/10) (localFailureTolerance M) M).prod (signLaw M))
        {w | BudgetedSuccess F ε γ (selectedBudgetedRun P ν (ε/10) γ κ f routine w)} := by
  dsimp only
  constructor
  · intro w
    have hw : ((selectedBudgetedRun P ν (ε/10) γ κ f routine w).2.1 : ℝ) ≤
        (selectedQueryCap P ν (ε/10) γ κ : ℝ) := by
      exact_mod_cast selectedBudgetedRun_spent_le P ν (ε/10) γ κ f routine w
    exact hw.trans_lt (selectedQueryCap_epsilon_rate P h.nu_pos hε hε1 hγ hγ1 hE hκ)
  · exact h.selectedBudgetedRun_epsilon_success hε hγ hm hc κ

/-- The same selected cap specializes to the Lipschitz-Hessian endpoint;
the identical explicit single-curvature price condition is retained. -/
theorem selectedQueryCap_lipschitz_rate (P : Parameters) {ε γ E : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hE : 0 ≤ E)
    {κ : ℕ} (hκ : (κ : ℝ) ≤ E*(toleranceLog ε γ)^4/γ^2) :
    (selectedQueryCap P 1 (ε/10) γ κ : ℝ) <
      epsilonQueryCoefficient P 1 E*(toleranceLog ε γ)^4*(1/ε^3+1/γ^5) := by
  simpa only [holderEndpointRate_lipschitz ε hγ.le] using
    selectedQueryCap_epsilon_rate P (by norm_num : (0 : ℝ) < 1) hε hε1 hγ hγ1 hE hκ

end
end SecondOrder
