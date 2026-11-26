import Bilevel.SmallGapMean
import Bilevel.SmallGapHyperSmoothness
import Bilevel.SmallGapSignal

/-! Explicit universal constants for the original small-gap scaling.
The radius is fixed first and the accuracy constant second. All side
conditions follow from the original high-accuracy range, with no gap restriction. -/

noncomputable section
namespace Bilevel.SmallGapScaling
open SmallGapInstance SmallGapLiftSupport

def radiusConstant : ℝ := (8192 * C ^ 2)⁻¹
def accuracyConstant : ℝ := radiusConstant / 1024

theorem radiusConstant_pos : 0 < radiusConstant := by
  have h := C_pos
  unfold radiusConstant
  positivity
theorem radiusConstant_le_one : radiusConstant ≤ 1 := by
  unfold radiusConstant
  apply inv_le_one_of_one_le₀
  have hC := C_one_le
  nlinarith
theorem accuracyConstant_pos : 0 < accuracyConstant := div_pos radiusConstant_pos (by norm_num)

structure Input where
  L : ℝ
  κ : ℝ
  θ : ℝ
  ε : ℝ
  L_pos : 0 < L
  κ_ge_two : 2 ≤ κ
  θ_ge_one : 1 ≤ θ
  θ_le_κ : θ ≤ κ
  ε_pos : 0 < ε
  accuracy : ε ≤ accuracyConstant * L / (θ * κ)

namespace Input
variable (Q : Input)

theorem κ_pos : 0 < Q.κ := by linarith [Q.κ_ge_two]
theorem θ_pos : 0 < Q.θ := lt_of_lt_of_le zero_lt_one Q.θ_ge_one
theorem θκ_ge_one : 1 ≤ Q.θ * Q.κ :=
  one_le_mul_of_one_le_of_one_le Q.θ_ge_one (by linarith [Q.κ_ge_two])

theorem accuracy_multiplied : 1024 * Q.θ * Q.κ * Q.ε ≤ radiusConstant * Q.L := by
  have h := (le_div_iff₀ (mul_pos Q.θ_pos Q.κ_pos)).mp Q.accuracy
  unfold accuracyConstant at h
  linarith

theorem accuracy_weak : 1024 * Q.ε ≤ radiusConstant * Q.L := by
  have h := mul_le_mul_of_nonneg_right Q.θκ_ge_one
    (show 0 ≤ (1024 : ℝ) * Q.ε from mul_nonneg (by norm_num) Q.ε_pos.le)
  nlinarith [Q.accuracy_multiplied]

theorem width : 34 * (8 * Q.ε / (Q.κ * (Q.L * Q.θ))) ≤ radiusConstant / Q.θ := by
  apply (le_div_iff₀ Q.θ_pos).mpr
  have he : 34 * (8 * Q.ε / (Q.κ * (Q.L * Q.θ))) * Q.θ =
      272 * Q.ε / (Q.κ * Q.L) := by
    field_simp [Q.θ_pos.ne', Q.κ_pos.ne', Q.L_pos.ne']
    ring
  rw [he]
  apply (div_le_iff₀ (mul_pos Q.κ_pos Q.L_pos)).mpr
  have h := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Q.κ by linarith [Q.κ_ge_two])
    (mul_nonneg radiusConstant_pos.le Q.L_pos.le)
  nlinarith [Q.accuracy_weak, Q.ε_pos]

def parameters : Parameters where
  μ := Q.L / Q.κ
  L := Q.L
  S := Q.L * Q.θ
  R := radiusConstant / Q.θ
  δ := 8 * Q.ε / (Q.κ * (Q.L * Q.θ))
  μ_pos := div_pos Q.L_pos Q.κ_pos
  L_pos := Q.L_pos
  S_pos := mul_pos Q.L_pos Q.θ_pos
  R_pos := div_pos radiusConstant_pos Q.θ_pos
  δ_pos := by have := Q.ε_pos; have := Q.L_pos; have := Q.κ_pos; have := Q.θ_pos; positivity
  μ_le_L := by
    apply (div_le_iff₀ Q.κ_pos).mpr
    nlinarith [Q.L_pos, Q.κ_ge_two]
  width := Q.width

theorem condition_number : Q.parameters.L / Q.parameters.μ = Q.κ := by
  change Q.L / (Q.L / Q.κ) = Q.κ
  field_simp [Q.L_pos.ne', Q.κ_pos.ne']

theorem gamma : (Q.parameters.L / Q.parameters.μ) * Q.parameters.S * Q.parameters.δ = 8 * Q.ε := by
  rw [Q.condition_number]
  dsimp [parameters]
  field_simp [Q.L_pos.ne', Q.κ_pos.ne', Q.θ_pos.ne']

theorem Gamma : (Q.parameters.L / Q.parameters.μ) ^ 2 * Q.parameters.S = Q.κ ^ 2 * (Q.L * Q.θ) := by
  rw [Q.condition_number]
  rfl

theorem scale_condition : 4096 * C ^ 2 * Q.parameters.S * Q.parameters.R ≤ Q.parameters.L := by
  have hC := C_pos
  have hθ := Q.θ_pos
  have he : 4096 * C ^ 2 * Q.parameters.S * Q.parameters.R = Q.L / 2 := by
    dsimp [parameters, radiusConstant]
    field_simp
    ring
  rw [he]
  change Q.L / 2 ≤ Q.L
  linarith [Q.L_pos]

theorem geometry : Q.parameters.Geometry := by
  constructor
  · rw [Q.condition_number]
    change (radiusConstant / Q.θ) / Q.κ ≤ 1
    rw [div_div]
    apply (div_le_one (mul_pos Q.θ_pos Q.κ_pos)).mpr
    exact radiusConstant_le_one.trans Q.θκ_ge_one
  · rw [Q.gamma, Q.condition_number]
    change 8 * Q.ε ≤ Q.L * (radiusConstant / Q.θ) / (2 * Q.κ)
    have he : Q.L * (radiusConstant / Q.θ) / (2 * Q.κ) =
        radiusConstant * Q.L / (2 * Q.θ * Q.κ) := by ring
    rw [he]
    apply (le_div_iff₀ (by have := Q.θ_pos; have := Q.κ_pos; positivity : 0 < 2 * Q.θ * Q.κ)).mpr
    have hp : 0 < Q.θ * Q.κ * Q.ε := by have := Q.ε_pos; have := Q.θ_pos; have := Q.κ_pos; positivity
    nlinarith [Q.accuracy_multiplied]

theorem S_ge_L : Q.parameters.L ≤ Q.parameters.S := by
  change Q.L ≤ Q.L * Q.θ
  nlinarith [Q.L_pos, Q.θ_ge_one]

end Input
end Bilevel.SmallGapScaling
