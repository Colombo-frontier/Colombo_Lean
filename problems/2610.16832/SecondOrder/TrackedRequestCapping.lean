import SecondOrder.TrackedRequestBudget

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

theorem requestCharge_length {d : ℕ} (trace : List (TrackingRequest d)) :
    trace.length = requestCharge isAnchorRequest trace+requestCharge isChordRequest trace+
      requestCharge isCurvatureRequest trace := by
  induction trace with
  | nil => simp [requestCharge]
  | cons r trace ih =>
    simp only [requestCharge,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    cases r <;> simp only [isAnchorRequest,isChordRequest,isCurvatureRequest] <;> omega

/-- Deterministic total local-call bound for the chronological schedule.
It holds on failed-reply paths too and includes the initial anchor. -/
theorem trackedRequestTrace_length_le {d L M q : ℕ} (hq : 0 < q) (Lip s τ : ℝ)
    (source : TrackingSource d L) (w : Fin M → Bool) :
    (trackedRequestTrace q Lip s τ source M w).length ≤ 4*M+2 := by
  rw [requestCharge_length]
  have ha := trackedRequestTrace_anchors_le hq Lip s τ source M w
  have hc := trackedRequestTrace_chord_count hq Lip s τ source w
  have he := trackedRequestTrace_curvature_le q Lip s τ source M w
  have hn := idealPhysicalLength_le Lip s (trackedPolicy q Lip s τ source) w
  rw [trackedRun_physical] at he
  dsimp only [idealPhysicalLength,stateMoves] at hn hc
  omega

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d L : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- Tail bound for the corrected request charge. The separate online
budget-checking implementation still has to be coupled to this trace. -/
theorem CommonLoss.correctedTrackedTrace_over_budget (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ ρ δ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {source : Ξ → TrackingSource d L} (hm : MeasurableTrackingSource source) (M κ : ℕ) (hM : M ≤ 2^L)
    {Q : ℕ} (hQ : 0 < Q) :
    (η.prod (signLaw M)) {w | Q < requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
      (trackedRequestTrace q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ
        (correctTrackingSource F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ ρ hγ (source w.1)) M w.2)} ≤
      ENNReal.ofReal (trackingRequestBudget P ν τ γ ρ δ q L κ/(Q : ℝ)) := by
  have hi := h.correctedTrackedTrace_cost_integral (η := η) hq hτ hγ hρ hL hδ hδ1 hm M κ hM
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hb := (hi.1.div_const (Q : ℝ)).measure_le_integral
    (Filter.Eventually.of_forall (fun w => by positivity))
    (s := {w | Q < requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
      (trackedRequestTrace q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ
        (correctTrackingSource F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ ρ hγ (source w.1)) M w.2)})
    (fun w hw => by
      apply (le_div_iff₀ hQr).mpr
      simp only [one_mul]
      exact_mod_cast hw.le)
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div]
  exact div_le_div_of_nonneg_right hi.2 hQr.le

/-- Local failure is charged only once when combining physical stopping
and total request cost. εfail remains an explicit input to be supplied by
the fresh-sampling implementation, and κ remains a per-curvature price. -/
theorem CommonLoss.trackedRun_trace_failure_bound (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ ρ δ εfail : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ εfail)
    {source : Ξ → TrackingSource d L} (hm : MeasurableTrackingSource source)
    (M κ : ℕ) (hM : 0 < M) (hdepth : M ≤ 2^L) {Q : ℕ} (hQ : 0 < Q)
    (hfail : (η.prod (signLaw M)) {w | ¬ trackedHistoryGood F q P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) τ γ ρ (source w.1) M w.2} ≤ ENNReal.ofReal εfail) :
    (η.prod (signLaw M)) {w |
      (trackedRun q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ (source w.1) M w.2).physical.running = true ∨
      ¬ IsSOSP F (10*τ) γ (trackedRun q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ (source w.1) M w.2).physical.point ∨
      Q < requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
        (trackedRequestTrace q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ (source w.1) M w.2)} ≤
      ENNReal.ofReal (εfail+idealMoveBudget P ν τ γ/(M : ℝ)+trackingRequestBudget P ν τ γ ρ δ q L κ/(Q : ℝ)) := by
  let s := curvatureRadius P.hessianHolder ν γ
  let analysis := fun ξ => trackedAnalysisPolicy F q P.gradientLip s τ ρ hγ (source ξ)
  let corrected := fun ξ => correctTrackingSource F P.gradientLip s τ ρ hγ (source ξ)
  let bad := {w : Ξ × (Fin M → Bool) | ¬ trackedHistoryGood F q P.gradientLip s τ γ ρ (source w.1) M w.2}
  let running := {w : Ξ × (Fin M → Bool) | (idealRun P.gradientLip s (analysis w.1) M w.2).running = true}
  let spent := {w : Ξ × (Fin M → Bool) | Q < requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
    (trackedRequestTrace q P.gradientLip s τ (corrected w.1) M w.2)}
  have ham := trackedAnalysisPolicy_measurable h.population_smooth q P.gradientLip s τ ρ hγ hm
  have hav := fun ξ => trackedAnalysisPolicy_valid F q P.gradientLip s ρ hτ.le hγ (source ξ)
  have hcap := h.idealMixture_physical_cap (η := η) hτ hγ analysis hav hM
    (idealRun_total_moves_measurable P.gradientLip s ham M)
  have hcost := h.correctedTrackedTrace_over_budget (η := η) hq hτ hγ hρ hL hδ hδ1 hm M κ hdepth hQ
  have hi := h.correctedTrackedTrace_cost_integral (η := η) hq hτ hγ hρ hL hδ hδ1 hm M κ hdepth
  have hB0 : 0 ≤ trackingRequestBudget P ν τ γ ρ δ q L κ :=
    (integral_nonneg (fun w => Nat.cast_nonneg _)).trans hi.2
  have hsub : {w : Ξ × (Fin M → Bool) |
      (trackedRun q P.gradientLip s τ (source w.1) M w.2).physical.running = true ∨
      ¬ IsSOSP F (10*τ) γ (trackedRun q P.gradientLip s τ (source w.1) M w.2).physical.point ∨
      Q < requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
        (trackedRequestTrace q P.gradientLip s τ (source w.1) M w.2)} ⊆ bad ∪ (running ∪ spent) := by
    intro w hw
    by_cases hg : trackedHistoryGood F q P.gradientLip s τ γ ρ (source w.1) M w.2
    · right
      have he := trackedAnalysisPolicy_good_agrees F q P.gradientLip s hτ.le hγ hρ hL (source w.1) M w.2 hdepth hg
      rcases hw with hr | hs | hc
      · left
        change (idealRun P.gradientLip s (analysis w.1) M w.2).running = true
        rw [he]
        exact hr
      · left
        change (idealRun P.gradientLip s (analysis w.1) M w.2).running = true
        rw [he]
        cases hr : (trackedRun q P.gradientLip s τ (source w.1) M w.2).physical.running
        · exact False.elim (hs (trackedRun_good_stopped_sosp hτ.le hγ hρ hL q P.gradientLip s (source w.1) M w.2 hdepth hg hr))
        · rfl
      · right
        change Q < requestCharge _ (trackedRequestTrace q P.gradientLip s τ (corrected w.1) M w.2)
        rw [trackedRequestTrace_corrected_agrees F q P.gradientLip s hγ (source w.1) M w.2 hg]
        exact hc
    · exact Or.inl hg
  calc
    _ ≤ (η.prod (signLaw M)) (bad ∪ (running ∪ spent)) := measure_mono hsub
    _ ≤ (η.prod (signLaw M)) bad+((η.prod (signLaw M)) running+(η.prod (signLaw M)) spent) :=
      (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal εfail+(ENNReal.ofReal (idealMoveBudget P ν τ γ/(M : ℝ))+
        ENNReal.ofReal (trackingRequestBudget P ν τ γ ρ δ q L κ/(Q : ℝ))) := add_le_add hfail (add_le_add hcap hcost)
    _ = _ := by
      rw [← ENNReal.ofReal_add (div_nonneg (idealMoveBudget_nonneg P ν τ γ hγ) (Nat.cast_nonneg M))
        (div_nonneg hB0 (Nat.cast_nonneg Q)),← ENNReal.ofReal_add hε
        (add_nonneg (div_nonneg (idealMoveBudget_nonneg P ν τ γ hγ) (Nat.cast_nonneg M))
          (div_nonneg hB0 (Nat.cast_nonneg Q)))]
      congr 1
      ring

end
end SecondOrder
