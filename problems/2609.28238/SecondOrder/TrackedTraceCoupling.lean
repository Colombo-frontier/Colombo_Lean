import SecondOrder.TrackedChordSchedule
import SecondOrder.EpochCostCongruence

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

/-- On a successful history, local correction preserves every request and
its endpoints in chronological order, not just the final stored state. -/
theorem trackedRequestTrace_corrected_agrees {d L : ℕ} (F : Point d → ℝ) (q : ℕ) (Lip s : ℝ)
    {τ ρ γ : ℝ} (hγ : 0 < γ) (source : TrackingSource d L) (t : ℕ) (w : Fin t → Bool)
    (hg : trackedHistoryGood F q Lip s τ γ ρ source t w) :
    trackedRequestTrace q Lip s τ (correctTrackingSource F Lip s τ ρ hγ source) t w =
      trackedRequestTrace q Lip s τ source t w := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [trackedRequestTrace,trackedRequestTrace,ih (Fin.init w) hg.1,
      trackedRun_corrected_agrees F q Lip s hγ source t (Fin.init w) hg.1]
    dsimp only [correctTrackingSource]
    rw [correctTrackedCurvature_unchanged F τ hγ _ _ hg.2.1]

theorem trackedAnalysisPath_agrees {d L M : ℕ} (F : Point d → ℝ) (q : ℕ) (Lip s : ℝ)
    {τ γ ρ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ) (hL : (L : ℝ)*ρ ≤ τ/4)
    (source : TrackingSource d L) (w : Fin M → Bool) (hM : M ≤ 2^L) :
    ∀ t ≤ M, idealPath Lip s (trackedAnalysisPolicy F q Lip s τ ρ hγ source) (extendSigns w) t =
      idealPath Lip s (trackedPolicy q Lip s τ (correctTrackingSource F Lip s τ ρ hγ source)) (extendSigns w) t := by
  intro t ht
  unfold idealPath
  rw [trackedAnalysisPolicy_agrees F q Lip s hτ hγ hρ hL source t _ (ht.trans hM),trackedRun_physical]

theorem correctedTrackedTrace_chord_cost {d L M q : ℕ} (F : Point d → ℝ) (P : Parameters)
    (hq : 0 < q) (Lip s : ℝ) {τ γ ρ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (δ : ℝ) (source : TrackingSource d L) (w : Fin M → Bool) (hM : M ≤ 2^L) :
    requestCharge (requestChordCost P ρ δ)
      (trackedRequestTrace q Lip s τ (correctTrackingSource F Lip s τ ρ hγ source) M w) =
        idealEpochTreeQueries P q Lip s (trackedAnalysisPolicy F q Lip s τ ρ hγ source) w L ρ δ := by
  rw [trackedRequestTrace_chord_cost P hq]
  exact (idealEpochTreeQueries_congr P q Lip s _ _ w
    (trackedAnalysisPath_agrees F q Lip s hτ hγ hρ hL source w hM) L ρ δ).symm

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d L : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The full chronological chord request trace of the locally corrected
stored tracker inherits the model-parameter query bound. Request endpoint
geometry, counts, and integrability are conclusions of the construction. -/
theorem CommonLoss.correctedTrackedTrace_chord_integral (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ ρ δ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {source : Ξ → TrackingSource d L} (hm : MeasurableTrackingSource source) (M : ℕ) (hM : M ≤ 2^L) :
    let cost := fun w : Ξ × (Fin M → Bool) =>
      (requestCharge (requestChordCost P ρ δ)
        (trackedRequestTrace q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ
          (correctTrackingSource F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ ρ hγ (source w.1)) M w.2) : ℝ)
    Integrable cost (η.prod (signLaw M)) ∧
      (∫ w, cost w ∂η.prod (signLaw M)) ≤ epochTreeBudget P ν τ γ ρ δ q L := by
  dsimp only
  simp_rw [correctedTrackedTrace_chord_cost F P hq P.gradientLip
    (curvatureRadius P.hessianHolder ν γ) hτ.le hγ hρ hL δ _ _ hM]
  exact h.idealEpochTreeQueries_integral hq hτ hγ
    (trackedAnalysisPolicy_measurable h.population_smooth q P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) τ ρ hγ hm)
    (fun ξ => trackedAnalysisPolicy_valid F q P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) ρ hτ.le hγ (source ξ)) M L hδ hδ1

end
end SecondOrder
