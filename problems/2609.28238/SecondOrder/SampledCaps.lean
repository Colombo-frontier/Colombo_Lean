import SecondOrder.SampledExecutionBound

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

theorem trackingRequestBudget_nonneg (P : Parameters) (ν τ γ ρ δ : ℝ) (q L κ : ℕ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ trackingRequestBudget P ν τ γ ρ δ q L κ := by
  have hΔ := P.gap_pos
  have hLip := P.gradientLip_pos
  have hC := chordCostCoefficient_nonneg P ρ
  have hR := chordConfidenceFactor_nonneg hδ hδ1
  have hB := idealMoveBudget_nonneg P ν τ γ hγ
  dsimp only [trackingRequestBudget,epochTreeBudget]
  positivity

variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {d L : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure Ψ} [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.finiteTrackingLaw_failure_one_ninety_sixth (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) (Lip s γ : ℝ) {τ ρ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ)
    (M : ℕ) {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤ ENNReal.ofReal (localFailureTolerance M)) :
    ((finiteTrackingLaw μ η P L τ (localFailureTolerance M) M).prod (signLaw M))
      {w | ¬trackedHistoryGood F q Lip s τ γ ρ
        (finiteActualSource P f q Lip s τ ρ (localFailureTolerance M) routine M w.1) M w.2} ≤
          ENNReal.ofReal (1/96 : ℝ) :=
  (h.finiteTrackingLaw_failure hq Lip s γ hτ hρ (localFailureTolerance_pos M) hm hc M).trans
    (ENNReal.ofReal_le_ofReal (localFailureTolerance_total M))

/-- With the manuscript's local tolerance and explicit physical/query
price caps, failure of the actual sampled trace has probability at most
3/32. This is a trace-price event bound, not yet a theorem about an online
budget-checking oracle program; the curvature routine and price κ remain
explicit inputs. -/
theorem CommonLoss.sampledExecution_caps (h : CommonLoss μ P ν F f)
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
    let source := finiteActualSource (L := L) P f q P.gradientLip s τ ρ δ routine M
    ((finiteTrackingLaw μ η P L τ δ M).prod (signLaw M)) {w |
      (trackedRun q P.gradientLip s τ (source w.1) M w.2).physical.running = true ∨
      ¬IsSOSP F (10*τ) γ (trackedRun q P.gradientLip s τ (source w.1) M w.2).physical.point ∨
      Q < requestCharge (requestOracleCost P τ ρ δ (fun _ => κ)) (trackedRequestTrace q P.gradientLip s τ (source w.1) M w.2)} ≤
        ENNReal.ofReal (3/32 : ℝ) := by
  dsimp only
  have hB := trackingRequestBudget_nonneg P ν τ γ ρ (localFailureTolerance (physicalCap P ν τ γ)) q L κ
    hγ (localFailureTolerance_pos _) (localFailureTolerance_le_one _)
  apply (h.sampledExecution_trace_failure hq hτ hγ hρ hL
    (localFailureTolerance_pos _) (localFailureTolerance_le_one _) hm hc
    (physicalCap P ν τ γ) κ (physicalCap_pos P ν τ γ hγ) hdepth (queryCap_pos hB)).trans
  apply ENNReal.ofReal_le_ofReal
  have ha := localFailureTolerance_total (physicalCap P ν τ γ)
  have hb := physicalCap_ratio P ν τ γ hγ
  have hc' := queryCap_ratio hB
  linarith

end
end SecondOrder
