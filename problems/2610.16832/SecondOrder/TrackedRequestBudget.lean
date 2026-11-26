import SecondOrder.TrackedTraceCoupling
import SecondOrder.QueryCapping

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

theorem requestOracleCost_decomposition {d : ℕ} (P : Parameters) (τ ρ δ : ℝ) (κ : ℕ)
    (trace : List (TrackingRequest d)) :
    requestCharge (requestOracleCost P τ ρ δ (fun _ => κ)) trace =
      requestCharge isAnchorRequest trace*localQueryCount (P.gradientNoise^2) (τ/4) δ+
        requestCharge (requestChordCost P ρ δ) trace+requestCharge isCurvatureRequest trace*κ := by
  induction trace with
  | nil => simp [requestCharge]
  | cons r trace ih =>
    simp only [requestCharge,List.map_cons,List.sum_cons] at ih ⊢
    cases r <;> simp only [requestOracleCost,isAnchorRequest,isCurvatureRequest,requestChordCost,
      Nat.add_mul,Nat.one_mul,Nat.zero_mul,Nat.zero_add,Nat.add_zero] <;> omega

theorem correctedTrackedTrace_anchor_cost {d L M q : ℕ} (F : Point d → ℝ) (P : Parameters)
    (hq : 0 < q) (Lip s : ℝ) {τ γ ρ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (δ : ℝ) (source : TrackingSource d L) (w : Fin M → Bool) (hM : M ≤ 2^L) :
    requestCharge isAnchorRequest
      (trackedRequestTrace q Lip s τ (correctTrackingSource F Lip s τ ρ hγ source) M w)*
        localQueryCount (P.gradientNoise^2) (τ/4) δ =
      idealAnchorQueryCount P q Lip s (τ/4) δ (trackedAnalysisPolicy F q Lip s τ ρ hγ source) w := by
  rw [trackedRequestTrace_anchors_eq hq,idealAnchorQueryCount,idealAnchorCount_eq hq,
    trackedAnalysisPolicy_agrees F q Lip s hτ hγ hρ hL source M w hM]

/-- Explicit charge envelope for the complete local request schedule. κ is
an input price for one curvature routine, not a proved eigensolver bound. -/
def trackingRequestBudget (P : Parameters) (ν τ γ ρ δ : ℝ) (q L κ : ℕ) : ℝ :=
  (1+(P.gap*P.gradientLip/τ^2)/(q : ℝ))*
    ((36*P.gradientNoise^2/(τ/4)^2+2)*(8*Real.log (1/δ)+2))+
  epochTreeBudget P ν τ γ ρ δ q L+
  (1+16*P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2))*(κ : ℝ)

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d L : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.measurableIdealRun_curvature_count (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M : ℕ) :
    let count := fun w : Ξ × (Fin M → Bool) =>
      ((idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2).curvatureMoves : ℝ)
    Integrable count (η.prod (signLaw M)) ∧ (∫ w, count w ∂η.prod (signLaw M)) ≤
      16*P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2) := by
  have hz := state_measurable_fields.mp
    (idealRun_measurable P.gradientLip (curvatureRadius P.hessianHolder ν γ) hm M)
  exact mixed_sign_mean_bound
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hz.2.2.2.1)
    (fun _ => Nat.cast_nonneg _) (fun ξ => (h.idealRun_statistics hτ hγ (policy ξ) (hv ξ) M).2.1)

theorem CommonLoss.correctedTrackedTrace_anchor_integral (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ ρ δ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {source : Ξ → TrackingSource d L} (hm : MeasurableTrackingSource source) (M : ℕ) (hM : M ≤ 2^L) :
    let cost := fun w : Ξ × (Fin M → Bool) =>
      ((requestCharge isAnchorRequest
        (trackedRequestTrace q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ
          (correctTrackingSource F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ ρ hγ (source w.1)) M w.2)*
        localQueryCount (P.gradientNoise^2) (τ/4) δ : ℕ) : ℝ)
    Integrable cost (η.prod (signLaw M)) ∧ (∫ w, cost w ∂η.prod (signLaw M)) ≤
      (1+(P.gap*P.gradientLip/τ^2)/(q : ℝ))*
        ((36*P.gradientNoise^2/(τ/4)^2+2)*(8*Real.log (1/δ)+2)) := by
  dsimp only
  simp_rw [correctedTrackedTrace_anchor_cost F P hq P.gradientLip
    (curvatureRadius P.hessianHolder ν γ) hτ.le hγ hρ hL δ _ _ hM]
  exact h.idealAnchorQueryCount_integral hq hτ hγ hδ hδ1
    (trackedAnalysisPolicy_measurable h.population_smooth q P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) τ ρ hγ hm)
    (fun ξ => trackedAnalysisPolicy_valid F q P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) ρ hτ.le hγ (source ξ)) M

theorem CommonLoss.correctedTrackedTrace_curvature_integral (h : CommonLoss μ P ν F f)
    (q : ℕ) {τ γ ρ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) {source : Ξ → TrackingSource d L}
    (hm : MeasurableTrackingSource source) (M : ℕ) (hM : M ≤ 2^L) :
    let count := fun w : Ξ × (Fin M → Bool) =>
      (requestCharge isCurvatureRequest
        (trackedRequestTrace q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ
          (correctTrackingSource F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ ρ hγ (source w.1)) M w.2) : ℝ)
    Integrable count (η.prod (signLaw M)) ∧ (∫ w, count w ∂η.prod (signLaw M)) ≤
      1+16*P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2) := by
  dsimp only
  let s := curvatureRadius P.hessianHolder ν γ
  let policy := fun ξ => trackedAnalysisPolicy F q P.gradientLip s τ ρ hγ (source ξ)
  let corrected := fun ξ => correctTrackingSource F P.gradientLip s τ ρ hγ (source ξ)
  let count := fun w : Ξ × (Fin M → Bool) =>
    (requestCharge isCurvatureRequest (trackedRequestTrace q P.gradientLip s τ (corrected w.1) M w.2) : ℝ)
  let K := fun w : Ξ × (Fin M → Bool) => (idealRun P.gradientLip s (policy w.1) M w.2).curvatureMoves
  have hk := h.measurableIdealRun_curvature_count (η := η) hτ hγ
    (trackedAnalysisPolicy_measurable h.population_smooth q P.gradientLip s τ ρ hγ hm)
    (fun ξ => trackedAnalysisPolicy_valid F q P.gradientLip s ρ hτ.le hγ (source ξ)) M
  have hz := state_measurable_fields.mp (tracked_measurable_fields.mp
    (trackedRun_measurable q P.gradientLip s τ
      (correctTrackingSource_measurable h.population_smooth P.gradientLip s τ ρ hγ hm) M)).1
  have hc : Measurable count := by
    dsimp only [count]
    simp_rw [trackedRequestTrace_curvature]
    apply (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    exact hz.2.2.2.1.add (Measurable.ite (hz.2.1 (measurableSet_singleton true)) measurable_const measurable_const)
  have hb (w) : count w ≤ 1+(K w : ℝ) := by
    have hh := trackedRequestTrace_curvature_le q P.gradientLip s τ (corrected w.1) M w.2
    have he := trackedAnalysisPolicy_agrees F q P.gradientLip s hτ.le hγ hρ hL (source w.1) M w.2 hM
    change idealRun P.gradientLip s (policy w.1) M w.2=(trackedRun q P.gradientLip s τ (corrected w.1) M w.2).physical at he
    dsimp only [count,K]
    rw [he]
    exact_mod_cast hh
  have henv : Integrable (fun w => 1+(K w : ℝ)) (η.prod (signLaw M)) := (integrable_const 1).add hk.1
  have hi : Integrable count (η.prod (signLaw M)) := by
    apply henv.mono' hc.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hb w
  refine ⟨hi,(integral_mono hi henv hb).trans ?_⟩
  rw [integral_add (integrable_const 1) hk.1]
  simpa only [integral_const,measureReal_univ_eq_one,one_smul] using add_le_add_left hk.2 1

/-- Complete trace charge, with a stated per-curvature-routine price.
The remaining eigensolver proof must establish that price for a concrete
routine; this theorem does not insert an unproved eigenvalue complexity. -/
theorem CommonLoss.correctedTrackedTrace_cost_integral (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ ρ δ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hL : (L : ℝ)*ρ ≤ τ/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {source : Ξ → TrackingSource d L} (hm : MeasurableTrackingSource source) (M κ : ℕ) (hM : M ≤ 2^L) :
    let cost := fun w : Ξ × (Fin M → Bool) =>
      (requestCharge (requestOracleCost P τ ρ δ (fun _ => κ))
        (trackedRequestTrace q P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ
          (correctTrackingSource F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ ρ hγ (source w.1)) M w.2) : ℝ)
    Integrable cost (η.prod (signLaw M)) ∧
      (∫ w, cost w ∂η.prod (signLaw M)) ≤ trackingRequestBudget P ν τ γ ρ δ q L κ := by
  have ha := h.correctedTrackedTrace_anchor_integral (η := η) hq hτ hγ hρ hL hδ hδ1 hm M hM
  have hc := h.correctedTrackedTrace_chord_integral (η := η) hq hτ hγ hρ hL hδ hδ1 hm M hM
  have he := h.correctedTrackedTrace_curvature_integral (η := η) q hτ hγ hρ hL hm M hM
  dsimp only
  simp_rw [requestOracleCost_decomposition,Nat.cast_add]
  simp only [Nat.cast_mul] at ha ⊢
  refine ⟨(ha.1.add hc.1).add (he.1.mul_const (κ : ℝ)),?_⟩
  have hadd := integral_add (ha.1.add hc.1) (he.1.mul_const (κ : ℝ))
  simp only [Pi.add_apply] at hadd
  rw [hadd,integral_add ha.1 hc.1]
  simp only [integral_mul_const] at ha ⊢
  exact add_le_add (add_le_add ha.2 hc.2) (mul_le_mul_of_nonneg_right he.2 (Nat.cast_nonneg κ))

end
end SecondOrder
