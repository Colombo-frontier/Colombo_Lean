import SecondOrder.BorelCorrection

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

theorem idealRun_total_moves_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ}
    (L s : ℝ) {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (M : ℕ) :
    Measurable (fun w : Ξ × (Fin M → Bool) =>
      let z := idealRun L s (policy w.1) M w.2
      ((z.gradientMoves+z.curvatureMoves : ℕ) : ℝ)) := by
  have hz := state_measurable_fields.mp (idealRun_measurable L s hm M)
  exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hz.2.2.1.add hz.2.2.2.1)

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The measurable policy hypothesis now supplies all path measurability
needed for the energy theorem, so integrability is a conclusion. -/
theorem CommonLoss.measurableIdealRun_energy (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ x, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy x))
    (M : ℕ) :
    let z := fun w : Ξ × (Fin M → Bool) =>
      idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2
    (Integrable (fun w => (z w).gradientEnergy) (η.prod (signLaw M)) ∧
      (∫ w, (z w).gradientEnergy ∂η.prod (signLaw M)) ≤ P.gap/P.gradientLip) ∧
    (Integrable (fun w => (z w).curvatureEnergy) (η.prod (signLaw M)) ∧
      (∫ w, (z w).curvatureEnergy ∂η.prod (signLaw M)) ≤ 16*P.gap/(3*γ)) := by
  have hz := state_measurable_fields.mp
    (idealRun_measurable P.gradientLip (curvatureRadius P.hessianHolder ν γ) hm M)
  exact h.idealMixture_energy hτ hγ policy hv M hz.2.2.2.2.1 hz.2.2.2.2.2

/-- Full product-law physical coupling bound with arbitrary external
randomness. Unlike the earlier finite-sign lemma, the corrected trajectory
is now proved measurable from the measurable actual proposal policy. -/
theorem CommonLoss.measurable_corrected_failure_bound (h : CommonLoss μ P ν F f)
    {τ γ δ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) {M : ℕ} (hM : 0 < M)
    (hfail : (η.prod (signLaw M)) {w | ¬ validHistory F P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) τ γ (policy w.1) M w.2} ≤ ENNReal.ofReal δ) :
    (η.prod (signLaw M)) {w |
      (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2).running = true ∨
      ¬ IsSOSP F (10*τ) γ (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2).point}
      ≤ ENNReal.ofReal (δ+idealMoveBudget P ν τ γ/(M : ℝ)) := by
  let corrected := fun ξ => borelCorrectedPolicy F τ hγ (policy ξ)
  have hcm := borelCorrectedPolicy_measurable h.population_smooth τ hγ hm
  have hcv := fun ξ => borelCorrectedPolicy_valid F hτ.le hγ P.gradientLip
    (curvatureRadius P.hessianHolder ν γ) (policy ξ)
  have hcap := h.idealMixture_physical_cap (η := η) hτ hγ corrected hcv hM
    (idealRun_total_moves_measurable _ _ hcm M)
  have hsub : {w : Ξ × (Fin M → Bool) |
      (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2).running = true ∨
      ¬ IsSOSP F (10*τ) γ (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2).point} ⊆
      {w | ¬ validHistory F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy w.1) M w.2} ∪
      {w | (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (corrected w.1) M w.2).running = true} := by
    intro w hw
    by_cases hg : validHistory F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy w.1) M w.2
    · right
      have he := idealRun_borelCorrected_agrees F hγ P.gradientLip
        (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2 hg
      change (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (corrected w.1) M w.2).running = true
      rw [he]
      rcases hw with hr | hb
      · exact hr
      · cases hr : (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2).running
        · exact False.elim (hb (idealRun_good_stopped_sosp F hτ.le hγ _ _ (policy w.1) M w.2 hg hr))
        · rfl
    · exact Or.inl hg
  calc
    _ ≤ (η.prod (signLaw M))
      ({w | ¬ validHistory F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy w.1) M w.2} ∪
      {w | (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (corrected w.1) M w.2).running = true}) :=
        measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal δ+ENNReal.ofReal (idealMoveBudget P ν τ γ/(M : ℝ)) := add_le_add hfail hcap
    _ = _ := (ENNReal.ofReal_add hδ (div_nonneg (idealMoveBudget_nonneg P ν τ γ hγ) (Nat.cast_nonneg M))).symm

end
end SecondOrder
