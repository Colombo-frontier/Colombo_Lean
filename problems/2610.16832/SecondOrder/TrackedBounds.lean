import SecondOrder.TrackedHistoryMeasurability
import SecondOrder.MeasurableCapping

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

/-- An everywhere valid analysis policy. It follows the locally corrected
tracker throughout the finite depth horizon. The outer physical correction
only makes the policy valid after that horizon, so existing uniform energy
theorems can be applied without assuming an infinite-depth tracker. -/
def trackedAnalysisPolicy {d L : ℕ} (F : Point d → ℝ) (q : ℕ) (Lip s τ ρ : ℝ)
    {γ : ℝ} (hγ : 0 < γ) (source : TrackingSource d L) : IdealPolicy d :=
  borelCorrectedPolicy F τ hγ (trackedPolicy q Lip s τ (correctTrackingSource F Lip s τ ρ hγ source))

theorem trackedAnalysisPolicy_valid {d L : ℕ} (F : Point d → ℝ) (q : ℕ) (Lip s ρ : ℝ)
    {τ γ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (source : TrackingSource d L) :
    ValidIdealPolicy F Lip s τ γ (trackedAnalysisPolicy F q Lip s τ ρ hγ source) :=
  borelCorrectedPolicy_valid F hτ hγ Lip s _

theorem trackedAnalysisPolicy_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d L : ℕ}
    {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) (q : ℕ) (Lip s τ ρ : ℝ)
    {γ : ℝ} (hγ : 0 < γ) {source : Ξ → TrackingSource d L} (hm : MeasurableTrackingSource source) :
    MeasurableIdealPolicy (fun ξ => trackedAnalysisPolicy F q Lip s τ ρ hγ (source ξ)) :=
  borelCorrectedPolicy_measurable hF τ hγ
    (trackedPolicy_measurable q Lip s τ (correctTrackingSource_measurable hF Lip s τ ρ hγ hm))

theorem trackedAnalysisPolicy_agrees {d L : ℕ} (F : Point d → ℝ) (q : ℕ) (Lip s : ℝ)
    {τ γ ρ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ) (hL : (L : ℝ)*ρ ≤ τ/4)
    (source : TrackingSource d L) (t : ℕ) (w : Fin t → Bool) (ht : t ≤ 2^L) :
    idealRun Lip s (trackedAnalysisPolicy F q Lip s τ ρ hγ source) t w =
      (trackedRun q Lip s τ (correctTrackingSource F Lip s τ ρ hγ source) t w).physical := by
  rw [trackedRun_physical]
  exact idealRun_borelCorrected_agrees F hγ Lip s _ t w
    (trackedHistoryGood_validHistory hτ hρ hL q Lip s _ t w ht
      (correctedTrackingSource_good F Lip s hτ hρ hγ q source t w))

theorem trackedAnalysisPolicy_good_agrees {d L : ℕ} (F : Point d → ℝ) (q : ℕ) (Lip s : ℝ)
    {τ γ ρ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ) (hL : (L : ℝ)*ρ ≤ τ/4)
    (source : TrackingSource d L) (t : ℕ) (w : Fin t → Bool) (ht : t ≤ 2^L)
    (hg : trackedHistoryGood F q Lip s τ γ ρ source t w) :
    idealRun Lip s (trackedAnalysisPolicy F q Lip s τ ρ hγ source) t w =
      (trackedRun q Lip s τ source t w).physical := by
  rw [trackedAnalysisPolicy_agrees F q Lip s hτ hγ hρ hL source t w ht,
    trackedRun_corrected_agrees F q Lip s hγ source t w hg]

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d L : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The two actual stored physical energy counters of the locally corrected
execution inherit the descent bounds. No moment or valid-move hypothesis is
imposed on the reply providers. -/
theorem CommonLoss.correctedTrackedRun_energy (h : CommonLoss μ P ν F f)
    (q : ℕ) {τ γ ρ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) {source : Ξ → TrackingSource d L} (hm : MeasurableTrackingSource source)
    (M : ℕ) (hM : M ≤ 2^L) :
    let z := fun w : Ξ × (Fin M → Bool) =>
      (trackedRun q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ
        (correctTrackingSource F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ ρ hγ (source w.1)) M w.2).physical
    (Integrable (fun w => (z w).gradientEnergy) (η.prod (signLaw M)) ∧
      (∫ w, (z w).gradientEnergy ∂η.prod (signLaw M)) ≤ P.gap/P.gradientLip) ∧
    (Integrable (fun w => (z w).curvatureEnergy) (η.prod (signLaw M)) ∧
      (∫ w, (z w).curvatureEnergy ∂η.prod (signLaw M)) ≤ 16*P.gap/(3*γ)) := by
  have hh := h.measurableIdealRun_energy (η := η) hτ hγ
    (trackedAnalysisPolicy_measurable h.population_smooth q P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) τ ρ hγ hm)
    (fun ξ => trackedAnalysisPolicy_valid F q P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) ρ hτ.le hγ (source ξ)) M
  simpa only [trackedAnalysisPolicy_agrees F q P.gradientLip
    (curvatureRadius P.hessianHolder ν γ) hτ.le hγ hρ hL _ M _ hM] using hh

theorem CommonLoss.correctedTrackedRun_moves (h : CommonLoss μ P ν F f)
    (q : ℕ) {τ γ ρ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) {source : Ξ → TrackingSource d L} (hm : MeasurableTrackingSource source)
    (M : ℕ) (hM : M ≤ 2^L) :
    let count := fun w : Ξ × (Fin M → Bool) =>
      (stateMoves (trackedRun q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ
        (correctTrackingSource F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ ρ hγ (source w.1)) M w.2).physical : ℝ)
    Integrable count (η.prod (signLaw M)) ∧
      (∫ w, count w ∂η.prod (signLaw M)) ≤ idealMoveBudget P ν τ γ := by
  have hh := h.idealPhysicalLength_integral (η := η) hτ hγ
    (trackedAnalysisPolicy_measurable h.population_smooth q P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) τ ρ hγ hm)
    (fun ξ => trackedAnalysisPolicy_valid F q P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) ρ hτ.le hγ (source ξ)) M
  simpa only [idealPhysicalLength,trackedAnalysisPolicy_agrees F q P.gradientLip
    (curvatureRadius P.hessianHolder ν γ) hτ.le hγ hρ hL _ M _ hM] using hh

/-- Physical failure of the actual stored tracker is controlled by local
routine failure plus the descent-derived physical cap term. The local
failure probability is still an explicit input; freshness and query-budget
proofs must supply it for the eventual sampling implementation. -/
theorem CommonLoss.trackedRun_failure_bound (h : CommonLoss μ P ν F f)
    (q : ℕ) {τ γ ρ δ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (hL : (L : ℝ)*ρ ≤ τ/4) {source : Ξ → TrackingSource d L} (hm : MeasurableTrackingSource source)
    {M : ℕ} (hM : 0 < M) (hdepth : M ≤ 2^L)
    (hfail : (η.prod (signLaw M)) {w | ¬ trackedHistoryGood F q P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) τ γ ρ (source w.1) M w.2} ≤ ENNReal.ofReal δ) :
    (η.prod (signLaw M)) {w |
      (trackedRun q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ (source w.1) M w.2).physical.running = true ∨
      ¬ IsSOSP F (10*τ) γ (trackedRun q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ (source w.1) M w.2).physical.point}
      ≤ ENNReal.ofReal (δ+idealMoveBudget P ν τ γ/(M : ℝ)) := by
  simp only [trackedRun_physical]
  apply h.measurable_corrected_failure_bound hτ hγ hδ
    (trackedPolicy_measurable q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ hm) hM
  apply le_trans (measure_mono ?_) hfail
  intro w hw hg
  exact hw (trackedHistoryGood_validHistory hτ.le hρ hL q P.gradientLip
    (curvatureRadius P.hessianHolder ν γ) (source w.1) M w.2 hdepth hg)

end
end SecondOrder
