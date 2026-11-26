import SecondOrder.IdealCorrection

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def physicalCap (P : Parameters) (ν τ γ : ℝ) : ℕ :=
  ⌈24*(1+idealMoveBudget P ν τ γ)⌉₊

theorem idealMoveBudget_nonneg (P : Parameters) (ν τ γ : ℝ) (hγ : 0 < γ) :
    0 ≤ idealMoveBudget P ν τ γ := by
  have hΔ := P.gap_pos
  have hL := P.gradientLip_pos
  dsimp [idealMoveBudget]
  positivity

theorem physicalCap_pos (P : Parameters) (ν τ γ : ℝ) (hγ : 0 < γ) :
    0 < physicalCap P ν τ γ := by
  have hn := idealMoveBudget_nonneg P ν τ γ hγ
  have hc := Nat.le_ceil (24*(1+idealMoveBudget P ν τ γ))
  have hp : (0 : ℝ) < physicalCap P ν τ γ := by dsimp [physicalCap]; linarith
  exact Nat.cast_pos.mp hp

theorem physicalCap_ratio (P : Parameters) (ν τ γ : ℝ) (hγ : 0 < γ) :
    idealMoveBudget P ν τ γ/(physicalCap P ν τ γ : ℝ) ≤ 1/24 := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr (physicalCap_pos P ν τ γ hγ))).mpr
  have hc := Nat.le_ceil (24*(1+idealMoveBudget P ν τ γ))
  change 24*(1+idealMoveBudget P ν τ γ) ≤ (physicalCap P ν τ γ : ℝ) at hc
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.idealRun_physical_cap_twenty_fourth (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (policy : IdealPolicy d)
    (hv : ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ policy) :
    signLaw (physicalCap P ν τ γ) {w |
      (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy (physicalCap P ν τ γ) w).running = true}
      ≤ ENNReal.ofReal (1/24 : ℝ) :=
  (h.idealRun_physical_cap hτ hγ policy hv (physicalCap_pos P ν τ γ hγ)).trans
    (ENNReal.ofReal_le_ofReal (physicalCap_ratio P ν τ γ hγ))

/-- Failure at a finite physical cap can only come from an invalid actual
move or from the corrected process still running. This is a coupling statement
for physical moves; it does not yet include local sample budgets or epoch state. -/
theorem CommonLoss.corrected_run_failure_bound (h : CommonLoss μ P ν F f)
    {τ γ δ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (policy : IdealPolicy d) {M : ℕ} (hM : 0 < M)
    (hfail : signLaw M {w | ¬ validHistory F P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) τ γ policy M w} ≤ ENNReal.ofReal δ) :
    signLaw M {w |
      (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy M w).running = true ∨
      ¬ IsSOSP F (10*τ) γ (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy M w).point}
      ≤ ENNReal.ofReal (δ+idealMoveBudget P ν τ γ/(M : ℝ)) := by
  let corrected := correctedPolicy F hτ.le hγ policy
  have hcap := h.idealRun_physical_cap hτ hγ corrected
    (correctedPolicy_valid F hτ.le hγ _ _ policy) hM
  have hsub : {w |
      (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy M w).running = true ∨
      ¬ IsSOSP F (10*τ) γ (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy M w).point} ⊆
      {w | ¬ validHistory F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ policy M w} ∪
      {w | (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) corrected M w).running = true} := by
    intro w hw
    by_cases hg : validHistory F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ policy M w
    · right
      have he := idealRun_corrected_agrees F hτ.le hγ P.gradientLip
        (curvatureRadius P.hessianHolder ν γ) policy M w hg
      change (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) corrected M w).running = true
      rw [he]
      rcases hw with hr | hb
      · exact hr
      · cases hr : (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy M w).running
        · exact False.elim (hb (idealRun_good_stopped_sosp F hτ.le hγ _ _ policy M w hg hr))
        · rfl
    · exact Or.inl hg
  calc
    _ ≤ signLaw M ({w | ¬ validHistory F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ policy M w} ∪
      {w | (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) corrected M w).running = true}) :=
        measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal δ+ENNReal.ofReal (idealMoveBudget P ν τ γ/(M : ℝ)) := add_le_add hfail hcap
    _ = _ := (ENNReal.ofReal_add hδ (div_nonneg (idealMoveBudget_nonneg P ν τ γ hγ) (Nat.cast_nonneg M))).symm

end
end SecondOrder
