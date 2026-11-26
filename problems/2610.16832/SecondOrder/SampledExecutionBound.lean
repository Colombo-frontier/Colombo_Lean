import SecondOrder.FiniteTrackingLaw

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

def localFailureTolerance (M : ℕ) : ℝ := 1/(96*((4*M+4 : ℕ) : ℝ))

theorem localFailureTolerance_pos (M : ℕ) : 0 < localFailureTolerance M := by
  unfold localFailureTolerance
  positivity

theorem localFailureTolerance_le_one (M : ℕ) : localFailureTolerance M ≤ 1 := by
  unfold localFailureTolerance
  apply (div_le_iff₀ (by positivity)).mpr
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) M]

theorem localFailureTolerance_total (M : ℕ) :
    ((4*M+2 : ℕ) : ℝ)*localFailureTolerance M ≤ 1/96 := by
  unfold localFailureTolerance
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity)).mpr
  push_cast
  linarith

variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {d L : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {η : Measure Ψ} [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- Full finite local failure bound on the actual independent sample and
sign law. It covers the initial anchor, every necessary curvature call,
every old-epoch chord, and every refresh, with no independent-events
assumption and no extra tree-depth factor. -/
theorem CommonLoss.finiteTrackingLaw_failure (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) (Lip s γ : ℝ) {τ ρ δ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hδ : 0 < δ)
    {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤ ENNReal.ofReal δ) (M : ℕ) :
    ((finiteTrackingLaw μ η P L τ δ M).prod (signLaw M))
      {w | ¬trackedHistoryGood F q Lip s τ γ ρ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2} ≤
        ENNReal.ofReal (((4*M+2 : ℕ) : ℝ)*δ) := by
  have hb : MeasurableSet {w : FiniteTrackingTape Ω Ψ P L τ δ M × (Fin M → Bool) |
      ¬trackedHistoryGood F q Lip s τ γ ρ (finiteActualSource P f q Lip s τ ρ δ routine M w.1) M w.2} :=
    (trackedHistoryGood_measurableSet h.population_smooth q Lip s τ γ ρ
      (h.finiteActualSource_measurable (L := L) q Lip s τ ρ δ hm M) M).compl
  rw [Measure.prod_apply_symm (μ := finiteTrackingLaw μ η P L τ δ M) (ν := signLaw M) hb]
  calc
    _ ≤ ∫⁻ _ : Fin M → Bool, ENNReal.ofReal (((4*M+2 : ℕ) : ℝ)*δ) ∂signLaw M := by
      apply lintegral_mono
      intro b
      have hh := h.finiteTrackingLaw_failure_slice (η := η) (L := L) hq Lip s γ hτ hρ hδ hm hc (extendSigns b) M
      have hb' : (fun i : Fin M => extendSigns b i.val) = b := by
        funext i
        simp [extendSigns,i.isLt]
      rw [hb'] at hh
      exact hh
    _ = _ := by simp

/-- The finite actual sampler now supplies the formerly external full
local failure probability. Only the explicit curvature routine contract
and its per-call price remain inputs; online budget enforcement is a
separate coupling task. -/
theorem CommonLoss.sampledExecution_trace_failure (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ ρ δ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 < ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {routine : Point d → Ψ → CurvatureReply d}
    (hm : Measurable (fun w : Point d × Ψ => routine w.1 w.2))
    (hc : ∀ x, η {w | ¬ValidCurvatureReply F γ x (routine x w)} ≤ ENNReal.ofReal δ)
    (M κ : ℕ) (hM : 0 < M) (hdepth : M ≤ 2^L) {Q : ℕ} (hQ : 0 < Q) :
    let s := curvatureRadius P.hessianHolder ν γ
    let source := finiteActualSource (L := L) P f q P.gradientLip s τ ρ δ routine M
    ((finiteTrackingLaw μ η P L τ δ M).prod (signLaw M)) {w |
      (trackedRun q P.gradientLip s τ (source w.1) M w.2).physical.running = true ∨
      ¬IsSOSP F (10*τ) γ (trackedRun q P.gradientLip s τ (source w.1) M w.2).physical.point ∨
      Q < requestCharge (requestOracleCost P τ ρ δ (fun _ => κ)) (trackedRequestTrace q P.gradientLip s τ (source w.1) M w.2)} ≤
        ENNReal.ofReal (((4*M+2 : ℕ) : ℝ)*δ+idealMoveBudget P ν τ γ/(M : ℝ)+
          trackingRequestBudget P ν τ γ ρ δ q L κ/(Q : ℝ)) := by
  dsimp only
  exact h.trackedRun_trace_failure_bound (η := finiteTrackingLaw μ η P L τ δ M)
    hq hτ hγ hρ.le hL hδ hδ1 (mul_nonneg (Nat.cast_nonneg _) hδ.le)
    (h.finiteActualSource_measurable q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ ρ δ hm M)
    M κ hM hdepth hQ
    (h.finiteTrackingLaw_failure hq P.gradientLip (curvatureRadius P.hessianHolder ν γ) γ hτ hρ hδ hm hc M)

end
end SecondOrder
