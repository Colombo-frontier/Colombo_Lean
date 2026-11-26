import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! # Integer stage calibration for the sufficient smooth baseline -/

noncomputable section

namespace NCConcave16991.DenseSmoothCalibration

def stageCount (A ρ K : ℝ) : ℕ := ⌊A * ρ / (2 * K)⌋₊

theorem stageCount_bounds {A ρ K : ℝ} (hK : 0 < K) (hρ : 0 < ρ)
    (hlarge : 4 * K ≤ A * ρ) :
    2 ≤ stageCount A ρ K ∧
      A * ρ / (4 * K) ≤ (stageCount A ρ K : ℝ) ∧
      A * ρ / (8 * K) ≤ (stageCount A ρ K - 1 : ℕ) ∧
      K * (stageCount A ρ K : ℝ) / ρ ≤ A := by
  let x := A * ρ / (2 * K)
  have hx : 2 ≤ x := (le_div_iff₀ (mul_pos (by norm_num) hK)).mpr (by nlinarith)
  have hA : 0 ≤ A := le_of_lt (pos_of_mul_pos_left (lt_of_lt_of_le (by positivity : 0 < 4*K) hlarge) hρ.le)
  have hfloorLo : x - 1 < (stageCount A ρ K : ℝ) := by
    have hh := Nat.lt_floor_add_one x
    change x < (stageCount A ρ K : ℝ) + 1 at hh
    linarith
  have hfloorHi : (stageCount A ρ K : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hsR : (1 : ℝ) < stageCount A ρ K := by linarith
  have hsN : 1 < stageCount A ρ K := by exact_mod_cast hsR
  have hcast : ((stageCount A ρ K - 1 : ℕ) : ℝ) + 1 = (stageCount A ρ K : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ stageCount A ρ K)
  have hsHalf : x / 2 ≤ (stageCount A ρ K : ℝ) := by linarith
  have hjHalf : (stageCount A ρ K : ℝ) / 2 ≤ (stageCount A ρ K - 1 : ℕ) := by
    have hh : (2 : ℝ) ≤ stageCount A ρ K := by exact_mod_cast (show 2 ≤ stageCount A ρ K by omega)
    linarith
  have hs : A * ρ / (4 * K) ≤ (stageCount A ρ K : ℝ) := by
    convert hsHalf using 1 <;> dsimp [x] <;> ring
  have hj : A * ρ / (8 * K) ≤ (stageCount A ρ K - 1 : ℕ) := by
    have hh := (div_le_div_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2)).trans hjHalf
    convert hh using 1 <;> ring
  refine ⟨by omega, hs, hj, ?_⟩
  apply (div_le_iff₀ hρ).mpr
  have hh := (le_div_iff₀ (mul_pos (by norm_num) hK)).mp hfloorHi
  nlinarith

theorem calibrated_row_cost {A ρ K r s J : ℝ} (hA : 0 ≤ A) (hρ : 0 < ρ)
    (hK : 0 < K) (hr : 0 ≤ r) (hJ : A * ρ / (8 * K) ≤ J)
    (hrs : s / 32768 ≤ r * ρ) : A * s / (524288 * K) ≤ r * J / 2 := by
  have hj := mul_le_mul_of_nonneg_left hJ hr
  have hs := mul_le_mul_of_nonneg_left hrs (div_nonneg hA (show (0 : ℝ) ≤ 16 * K by positivity))
  calc
    A * s / (524288 * K) = (A / (16 * K)) * (s / 32768) := by ring
    _ ≤ (A / (16 * K)) * (r * ρ) := hs
    _ = (r * (A * ρ / (8 * K))) / 2 := by ring
    _ ≤ r * J / 2 := div_le_div_of_nonneg_right hj (by norm_num)

end NCConcave16991.DenseSmoothCalibration
