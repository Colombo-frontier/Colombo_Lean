import RandomizedFO2003.ObstructionProbability

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade
open scoped BigOperators ENNReal

variable {ε Δ L₁ L₂ : ℝ}
variable (S : FiniteSpectralDesign (degreeCount ε L₁ L₂) (lowerCurvature ε L₂)
  (upperCurvature L₁) (1 / (16 * lowerCurvature ε L₂)))

/-- A single actual sphere/Haar distribution is concentrated on the stated
function class and has joint success probability at most one third for
every full-history algorithm and private seed law. The multiplicities
precede those universal quantifiers. -/
theorem distributional_lower_bound (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hregime : ε ≤ parameterConstant * L₁ ^ 2 / L₂)
    (hmass : massThreshold ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ)))
    (T : ℕ) (hT : T < (stageIndex ε Δ L₂ + 1) * degreeCount ε L₁ L₂) :
    ∃ K : Fin S.size → ℕ, 0 < ∑ j, K j ∧
      (∀ᵐ p ∂S.cascadeParameterLaw K (stageIndex ε Δ L₂),
        Model.InFunctionClass (S.sampledCascadeFunction K (stageIndex ε Δ L₂) (rhsScale ε) p) Δ L₁ L₂) ∧
      ∀ (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (A : Model.Algorithm ((stageIndex ε Δ L₂ + 1) * ∑ j, K j) Seed),
        ((S.cascadeParameterLaw K (stageIndex ε Δ L₂)).prod ν)
          (Model.familySuccess A (S.sampledCascadeFunction K (stageIndex ε Δ L₂) (rhsScale ε)) ε T) ≤
            (1 / 3 : ℝ≥0∞) := by
  obtain ⟨K, htotal, hbudget⟩ := S.choose_terminal_budgets (lowerCurvature_pos hε hL₂)
    (rhsScale_pos hε) (stageIndex ε Δ L₂) T hT
  refine ⟨K, htotal, S.sampledCascade_inFunctionClass_ae hε hL₁ hL₂ hregime hmass K, ?_⟩
  intro Seed _ ν _ A
  obtain ⟨hspectral, hterminal⟩ := hbudget Seed ν A
  calc
    _ ≤ _ := S.sampled_success_probability_bound (lowerCurvature_pos hε hL₂) K
      (stageIndex ε Δ L₂) (rhsScale_pos hε) hε.le le_rfl ν A T (Fin.last (stageIndex ε Δ L₂))
    _ ≤ (1 / 6 : ℝ≥0∞) + 1 / 6 := add_le_add hspectral hterminal
    _ = 1 / 3 := by
      have h6 : (1 / 6 : ℝ≥0∞) ≠ ⊤ := (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne
      have h3 : (1 / 3 : ℝ≥0∞) ≠ ⊤ := (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne
      apply (ENNReal.toReal_eq_toReal (ENNReal.add_ne_top.mpr ⟨h6, h6⟩) h3).mp
      rw [ENNReal.toReal_add h6 h6]
      norm_num

end RandomizedFO2003.FiniteSpectralDesign
