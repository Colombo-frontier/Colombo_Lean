import RandomizedFO2003.RateScales
import RandomizedFO2003.CascadeCoordinatesStationarity

namespace RandomizedFO2003.Cascade

/-- One numerical constant can be used for both the accuracy regime and
the stage-degree rate. The oracle lower-bound proof may shrink it further. -/
noncomputable def parameterConstant : ℝ := min accuracyConstant lowerRateCoefficient

theorem parameterConstant_pos : 0 < parameterConstant := lt_min accuracyConstant_pos lowerRateCoefficient_pos

theorem accuracy_of_parameter_regime {ε L₁ L₂ : ℝ} (hL₂ : 0 < L₂)
    (hregime : ε ≤ parameterConstant * L₁ ^ 2 / L₂) :
    ε ≤ accuracyConstant * L₁ ^ 2 / L₂ :=
  hregime.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg L₁)) hL₂.le)

theorem parameter_spectral_design {ε L₁ L₂ : ℝ} (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hregime : ε ≤ parameterConstant * L₁ ^ 2 / L₂) :
    Nonempty (FiniteSpectralDesign (degreeCount ε L₁ L₂) (lowerCurvature ε L₂)
      (upperCurvature L₁) (1 / (16 * lowerCurvature ε L₂))) :=
  chosen_spectral_design hε hL₁ hL₂ (accuracy_of_parameter_regime hL₂ hregime)

theorem parameter_stage_degree_rate {ε Δ L₁ L₂ : ℝ} (hε : 0 < ε) (hΔ : 0 < Δ)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hregime : ε ≤ parameterConstant * L₁ ^ 2 / L₂)
    (hmass : massThreshold ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ))) :
    parameterConstant * Model.rate ε Δ L₁ L₂ ≤
      ((stageIndex ε Δ L₂ * degreeCount ε L₁ L₂ : ℕ) : ℝ) := by
  have hr : 0 ≤ Model.rate ε Δ L₁ L₂ := by unfold Model.rate; positivity
  exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hr).trans
    (chosen_stage_degree_rate hε hL₁ hL₂ (accuracy_of_parameter_regime hL₂ hregime) hmass)

end RandomizedFO2003.Cascade

namespace RandomizedFO2003.FiniteSpectralDesign

open SpectralCoordinates Cascade
open scoped BigOperators

variable {ε Δ L₁ L₂ : ℝ}
variable (S : FiniteSpectralDesign (degreeCount ε L₁ L₂) (lowerCurvature ε L₂)
  (upperCurvature L₁) (1 / (16 * lowerCurvature ε L₂)))

/-- The source's function-class proposition for the chosen scales and stage
floor. No smoothness, gap, or scalar budget is assumed separately: all follow
from the original parameter regime with fixed numerical constants. -/
theorem chosen_cascade_inFunctionClass (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hregime : ε ≤ parameterConstant * L₁ ^ 2 / L₂)
    (hmass : massThreshold ≤ Δ * L₂ ^ (1 / 2 : ℝ) * ε ^ (-(3 / 2 : ℝ)))
    (K : Fin S.size → ℕ)
    (U : Fin (stageIndex ε Δ L₂ + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (stageIndex ε Δ L₂ + 1) → BlockSpace K) (hu : ∀ i, ‖u i‖ ≤ 1) :
    Model.InFunctionClass (S.cascadeFunction K (stageIndex ε Δ L₂) U u (rhsScale ε)) Δ L₁ L₂ := by
  have ha := accuracy_of_parameter_regime hL₂ hregime
  have hs := stageArgument_large_of_mass hε hL₂ hmass
  exact S.cascadeFunction_inFunctionClass (lowerCurvature_pos hε hL₂) (upperCurvature_pos hL₁).le
    K (stageIndex ε Δ L₂) U u (rhsScale_pos hε) hu
    (chosen_gap_budget hε hL₂ (by linarith)) (chosen_second_budget hL₁ hL₂ ha) (chosen_third_budget hε hL₂)

/-- Near-stationarity at the same chosen scales, for the same standard
Euclidean function that belongs to the target function class. -/
theorem chosen_cascade_stationarity (hε : 0 < ε) (hL₂ : 0 < L₂)
    (K : Fin S.size → ℕ)
    (U : Fin (stageIndex ε Δ L₂ + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (stageIndex ε Δ L₂ + 1) → BlockSpace K) (hu : ∀ i, ‖u i‖ = 1)
    (hweight : ∀ i j, |SpectralCoordinates.weight K (u i) j - S.weight j| ≤ (1 / 32) * S.weight j)
    (x : Model.Space ((stageIndex ε Δ L₂ + 1) * ∑ j, K j))
    (hx : ‖gradient (S.cascadeFunction K (stageIndex ε Δ L₂) U u (rhsScale ε)) x‖ ≤ ε) :
    let N := stageIndex ε Δ L₂
    let d := S.cascade K N U u (rhsScale ε)
    let z := (cascadeCoordinates K N).symm x
    (∀ i, ‖z i‖ ≤ d.B) ∧
    (∀ i, |forcingReadout (d.b i) d.D (z i)| ≤ d.K) ∧
    (∀ i, d.gate i (z i) = 1) ∧
    ‖d.A (Fin.last N) (z (Fin.last N)) - d.b (Fin.last N)‖ ≤ ε :=
  S.cascadeFunction_stationarity (lowerCurvature_pos hε hL₂) K (stageIndex ε Δ L₂) U u
    (rhsScale_pos hε) hε.le le_rfl hu hweight x hx

end RandomizedFO2003.FiniteSpectralDesign
