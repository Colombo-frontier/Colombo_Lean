import SecondOrder.FiniteBudgetCoupling

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

def BudgetedSuccess {d L : ℕ} (F : Point d → ℝ) (ε γ : ℝ) (z : QueryBudgetState (TrackedState d L)) : Prop :=
  z.2.2 = false ∧ z.1.physical.running = false ∧ IsSOSP F ε γ z.1.physical.point

theorem budgetedSuccess_iff_not_failure {d L : ℕ} (F : Point d → ℝ) (ε γ : ℝ)
    (z : QueryBudgetState (TrackedState d L)) : BudgetedSuccess F ε γ z ↔ ¬BudgetedFailure F ε γ z := by
  cases hr : z.2.2 <;> cases hs : z.1.physical.running <;> simp [BudgetedSuccess,BudgetedFailure,hr,hs]

variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {d L : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure Ψ} [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The full finite failure estimate now concerns the actual budgeted
sampler, including its initial rejection and both per-step checks.
The measurable curvature routine and its confidence bound remain inputs. -/
theorem CommonLoss.budgetedExecution_failure (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ ρ δ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 < ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤ ENNReal.ofReal δ)
    (M κ : ℕ) (hM : 0 < M) (hdepth : M ≤ 2^L) {Q : ℕ} (hQ : 0 < Q) :
    let s := curvatureRadius P.hessianHolder ν γ
    ((finiteTrackingLaw μ η P L τ δ M).prod (signLaw M)) {w |
      BudgetedFailure F (10*τ) γ (finiteBudgetedRun P f q Q κ P.gradientLip s τ ρ δ routine M w)} ≤
        ENNReal.ofReal (((4*M+2 : ℕ) : ℝ)*δ+idealMoveBudget P ν τ γ/(M : ℝ)+
          trackingRequestBudget P ν τ γ ρ δ q L κ/(Q : ℝ)) := by
  dsimp only
  simp only [finiteBudgetedRun_failure_iff]
  exact h.sampledExecution_trace_failure hq hτ hγ hρ hL hδ hδ1 hm hc M κ hM hdepth hQ

/-- With explicit manuscript caps, budget rejection, physical exhaustion
and an invalid output together have probability at most 3/32. The price κ
is reserved before invoking the supplied curvature routine. -/
theorem CommonLoss.budgetedExecution_caps (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ ρ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 < ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (hdepth : physicalCap P ν τ γ ≤ 2^L)
    {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤
      ENNReal.ofReal (localFailureTolerance (physicalCap P ν τ γ))) (κ : ℕ) :
    let M := physicalCap P ν τ γ
    let δ := localFailureTolerance M
    let s := curvatureRadius P.hessianHolder ν γ
    let Q := queryCap (trackingRequestBudget P ν τ γ ρ δ q L κ)
    ((finiteTrackingLaw μ η P L τ δ M).prod (signLaw M)) {w |
      BudgetedFailure F (10*τ) γ (finiteBudgetedRun P f q Q κ P.gradientLip s τ ρ δ routine M w)} ≤
        ENNReal.ofReal (3/32 : ℝ) := by
  dsimp only
  simp only [finiteBudgetedRun_failure_iff]
  exact h.sampledExecution_caps hq hτ hγ hρ hL hdepth hm hc κ

/-- Success means the budget was not rejected, the run stopped, and its
actual output is a (10τ,γ)-SOSP. This still requires an input curvature
routine satisfying the displayed uniform probability contract. -/
theorem CommonLoss.budgetedExecution_success (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ ρ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 < ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (hdepth : physicalCap P ν τ γ ≤ 2^L)
    {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤
      ENNReal.ofReal (localFailureTolerance (physicalCap P ν τ γ))) (κ : ℕ) :
    let M := physicalCap P ν τ γ
    let δ := localFailureTolerance M
    let s := curvatureRadius P.hessianHolder ν γ
    let Q := queryCap (trackingRequestBudget P ν τ γ ρ δ q L κ)
    ENNReal.ofReal (29/32 : ℝ) ≤ ((finiteTrackingLaw μ η P L τ δ M).prod (signLaw M)) {w |
      BudgetedSuccess F (10*τ) γ (finiteBudgetedRun P f q Q κ P.gradientLip s τ ρ δ routine M w)} := by
  dsimp only
  let M := physicalCap P ν τ γ
  let δ := localFailureTolerance M
  let s := curvatureRadius P.hessianHolder ν γ
  let Q := queryCap (trackingRequestBudget P ν τ γ ρ δ q L κ)
  let bad := {w : FiniteTrackingTape Ω Ψ P L τ δ M × (Fin M → Bool) |
    BudgetedFailure F (10*τ) γ (finiteBudgetedRun P f q Q κ P.gradientLip s τ ρ δ routine M w)}
  have hb : MeasurableSet bad := budgetedFailure_measurableSet h.population_smooth (10*τ) γ
    (h.finiteBudgetedRun_measurable q Q κ P.gradientLip s τ ρ δ hm M)
  have he : {w : FiniteTrackingTape Ω Ψ P L τ δ M × (Fin M → Bool) |
      BudgetedSuccess F (10*τ) γ (finiteBudgetedRun P f q Q κ P.gradientLip s τ ρ δ routine M w)} = badᶜ := by
    ext w
    exact budgetedSuccess_iff_not_failure F (10*τ) γ _
  change ENNReal.ofReal (29/32 : ℝ) ≤ ((finiteTrackingLaw μ η P L τ δ M).prod (signLaw M)) _
  rw [he,measure_compl hb (measure_ne_top _ _),measure_univ]
  calc
    ENNReal.ofReal (29/32 : ℝ) = 1-ENNReal.ofReal (3/32 : ℝ) := by
      rw [← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 3/32)]
      norm_num
    _ ≤ _ := tsub_le_tsub_left (h.budgetedExecution_caps hq hτ hγ hρ hL hdepth hm hc κ) 1

end
end SecondOrder
