import RandomizedFO2003.NumericalScales
import RandomizedFO2003.InverseApproximation
import Mathlib.Algebra.Order.Floor.Semiring

namespace RandomizedFO2003.Cascade

noncomputable def stageArgument (ε Δ L₂ : ℝ) : ℝ :=
  Δ * lowerCurvature ε L₂ / (2 * forcingAmplitude * (rhsScale ε) ^ 2)

noncomputable def degreeArgument (ε L₁ L₂ : ℝ) : ℝ :=
  (1 / 16 : ℝ) * Real.sqrt (upperCurvature L₁ / lowerCurvature ε L₂)

/-- The cascade has `stageIndex + 1` blocks; retaining one extra block makes
the endpoint convention compatible with the existing static construction. -/
noncomputable def stageIndex (ε Δ L₂ : ℝ) : ℕ := ⌊stageArgument ε Δ L₂⌋₊
noncomputable def degreeCount (ε L₁ L₂ : ℝ) : ℕ := ⌊degreeArgument ε L₁ L₂⌋₊

theorem stageArgument_pos {ε Δ L₂ : ℝ} (hε : 0 < ε) (hΔ : 0 < Δ) (hL₂ : 0 < L₂) :
    0 < stageArgument ε Δ L₂ := by
  have hh := rhsScale_pos hε
  have hγ := lowerCurvature_pos hε hL₂
  unfold stageArgument forcingAmplitude
  positivity

theorem degreeArgument_pos {ε L₁ L₂ : ℝ} (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) :
    0 < degreeArgument ε L₁ L₂ :=
  mul_pos (by norm_num) (Real.sqrt_pos.mpr (div_pos (upperCurvature_pos hL₁) (lowerCurvature_pos hε hL₂)))

theorem degreeArgument_large {ε L₁ L₂ : ℝ} (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (haccuracy : ε ≤ accuracyConstant * L₁ ^ 2 / L₂) : 2 ≤ degreeArgument ε L₁ L₂ := by
  have hγ := lowerCurvature_pos hε hL₂
  have hc := lowerCurvature_small hL₁ hL₂ haccuracy
  have hratio : 1024 ≤ upperCurvature L₁ / lowerCurvature ε L₂ := by
    apply (le_div_iff₀ hγ).mpr
    unfold upperCurvature
    linarith
  have hs := Real.sq_sqrt (show 0 ≤ upperCurvature L₁ / lowerCurvature ε L₂ by linarith)
  have hnonneg := Real.sqrt_nonneg (upperCurvature L₁ / lowerCurvature ε L₂)
  unfold degreeArgument
  nlinarith

theorem degreeCount_large {ε L₁ L₂ : ℝ} (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (haccuracy : ε ≤ accuracyConstant * L₁ ^ 2 / L₂) : 2 ≤ degreeCount ε L₁ L₂ :=
  (Nat.le_floor_iff' (by decide : 2 ≠ 0)).mpr (degreeArgument_large hε hL₁ hL₂ haccuracy)

theorem degreeCount_spectral_bound {ε L₁ L₂ : ℝ} (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) :
    (degreeCount ε L₁ L₂ : ℝ) ≤
      (1 / 16 : ℝ) * Real.sqrt (upperCurvature L₁ / lowerCurvature ε L₂) :=
  Nat.floor_le (degreeArgument_pos hε hL₁ hL₂).le

theorem stageIndex_large {ε Δ L₂ : ℝ} (hstage : 2 ≤ stageArgument ε Δ L₂) :
    2 ≤ stageIndex ε Δ L₂ := (Nat.le_floor_iff' (by decide : 2 ≠ 0)).mpr hstage

theorem floor_half_bound {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

/-- The extra endpoint block is fully accounted for in the gap budget. -/
theorem chosen_gap_budget {ε Δ L₂ : ℝ} (hε : 0 < ε) (hL₂ : 0 < L₂)
    (hstage : 1 ≤ stageArgument ε Δ L₂) :
    ((stageIndex ε Δ L₂ + 1 : ℕ) : ℝ) * forcingAmplitude *
      ((rhsScale ε) ^ 2 / lowerCurvature ε L₂) ≤ Δ := by
  have hh := rhsScale_pos hε
  have hγ := lowerCurvature_pos hε hL₂
  have hn : ((stageIndex ε Δ L₂ + 1 : ℕ) : ℝ) ≤ 2 * stageArgument ε Δ L₂ := by
    have hf := Nat.floor_le (show 0 ≤ stageArgument ε Δ L₂ by linarith)
    change ((⌊stageArgument ε Δ L₂⌋₊ + 1 : ℕ) : ℝ) ≤ _
    push_cast
    linarith
  calc
    _ = ((stageIndex ε Δ L₂ + 1 : ℕ) : ℝ) *
        (forcingAmplitude * ((rhsScale ε) ^ 2 / lowerCurvature ε L₂)) := by ring
    _ ≤ (2 * stageArgument ε Δ L₂) *
        (forcingAmplitude * ((rhsScale ε) ^ 2 / lowerCurvature ε L₂)) := by
      apply mul_le_mul_of_nonneg_right hn
      unfold forcingAmplitude
      positivity
    _ = Δ := by
      unfold stageArgument forcingAmplitude
      field_simp
      ring

theorem floored_stage_degree_lower_bound {ε Δ L₁ L₂ : ℝ}
    (hstage : 2 ≤ stageArgument ε Δ L₂) (hdegree : 2 ≤ degreeArgument ε L₁ L₂) :
    (stageArgument ε Δ L₂ * degreeArgument ε L₁ L₂) / 4 ≤
      ((stageIndex ε Δ L₂ * degreeCount ε L₁ L₂ : ℕ) : ℝ) := by
  have hs := floor_half_bound hstage
  have hm := floor_half_bound hdegree
  have h := mul_le_mul hs hm (by linarith : 0 ≤ degreeArgument ε L₁ L₂ / 2) (Nat.cast_nonneg _)
  push_cast
  change _ ≤ (⌊stageArgument ε Δ L₂⌋₊ : ℝ) * (⌊degreeArgument ε L₁ L₂⌋₊ : ℝ)
  convert h using 1
  ring

/-- The actual finite spectral design now has its degree chosen by a floor
from the original problem parameters. -/
theorem chosen_spectral_design {ε L₁ L₂ : ℝ} (hε : 0 < ε) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (haccuracy : ε ≤ accuracyConstant * L₁ ^ 2 / L₂) :
    Nonempty (FiniteSpectralDesign (degreeCount ε L₁ L₂) (lowerCurvature ε L₂)
      (upperCurvature L₁) (1 / (16 * lowerCurvature ε L₂))) :=
  finite_spectral_design_sqrt_regime _ (by have h := degreeCount_large hε hL₁ hL₂ haccuracy; omega)
    _ _ (lowerCurvature_pos hε hL₂) (spectral_interval_separation hL₁ hL₂ haccuracy)
    (degreeCount_spectral_bound hε hL₁ hL₂)

end RandomizedFO2003.Cascade
