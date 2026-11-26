import RandomizedFO2003.TerminalEvent
import RandomizedFO2003.OracleAveraging

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade Rotations
open scoped BigOperators ENNReal NNReal

variable {ε Δ L₁ L₂ : ℝ}
variable (S : FiniteSpectralDesign (degreeCount ε L₁ L₂) (lowerCurvature ε L₂)
  (upperCurvature L₁) (1 / (16 * lowerCurvature ε L₂)))
variable {Seed : Type} [MeasurableSpace Seed]

/-- Assembly for the concrete hard-function construction. Every analytic,
measurability, and averaging premise has been discharged. The two remaining
premises are probability budgets under the very same unconditioned sphere/
Haar law; the terminal one is not proved by this theorem. -/
theorem hard_function_of_terminal_budgets (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hregime : ε ≤ parameterConstant * L₁ ^ 2 / L₂)
    (hmass : massThreshold ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ)))
    (K : Fin S.size → ℕ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Model.Algorithm ((stageIndex ε Δ L₂ + 1) * ∑ j, K j) Seed) (T : ℕ)
    (hspectral : Measure.pi (fun _ : Fin (stageIndex ε Δ L₂ + 1) =>
        Spherical.sphereLaw (BlockSpace K)) (S.cascadeGoodEvent K (stageIndex ε Δ L₂))ᶜ ≤ (1 / 6 : ℝ≥0∞))
    (hterminal : ((S.cascadeParameterLaw K (stageIndex ε Δ L₂)).prod ν)
      (S.terminalFlatEvent K (stageIndex ε Δ L₂) (rhsScale ε) A T (Fin.last (stageIndex ε Δ L₂)))ᶜ ≤
        (1 / 6 : ℝ≥0∞)) :
    ∃ f : Model.Space ((stageIndex ε Δ L₂ + 1) * ∑ j, K j) → ℝ,
      Model.InFunctionClass f Δ L₁ L₂ ∧ ν (Model.Success A f ε T) < (2 / 3 : ℝ≥0∞) := by
  have hbound : ((S.cascadeParameterLaw K (stageIndex ε Δ L₂)).prod ν)
      (Model.familySuccess A (S.sampledCascadeFunction K (stageIndex ε Δ L₂) (rhsScale ε)) ε T) ≤
        (1 / 3 : ℝ≥0∞) := by
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
  have hpq : (1 / 3 : ℝ≥0∞) < 2 / 3 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply (ENNReal.mul_lt_mul_right (by norm_num) (by norm_num)).mpr
    norm_num
  obtain ⟨p, hp, hs⟩ := Model.exists_hard_sample_of_joint_bound A
    (S.sampledCascadeFunction K (stageIndex ε Δ L₂) (rhsScale ε))
    (S.measurable_sampledCascadeOracle K (stageIndex ε Δ L₂) (rhsScale ε))
    (S.cascadeParameterLaw K (stageIndex ε Δ L₂)) ν
    (S.sampledCascade_inFunctionClass_ae hε hL₁ hL₂ hregime hmass K)
    hpq hbound
  exact ⟨S.sampledCascadeFunction K (stageIndex ε Δ L₂) (rhsScale ε) p, hp, hs⟩

end RandomizedFO2003.FiniteSpectralDesign
