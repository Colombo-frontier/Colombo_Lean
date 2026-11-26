import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace FullJet

/-- Exact high-order rescaling identities, equations (alpha-beta). -/
theorem rescaling_identities (p : ℕ) (χ L ρ H ε β : ℝ)
    (hχ : 0 < χ) (hρ : 0 < ρ) (hH : 0 < H) (hε : 0 < ε) (hβ : 0 < β)
    (hpow : β ^ p = χ * L * ρ / (8 * H * ε)) :
    let α := 8 * ε / (χ * β)
    α * β * χ = 8 * ε ∧ α * β ^ (p + 1) * H / ρ = L := by
  dsimp
  constructor
  · field_simp
    <;> ring
  · rw [pow_succ, hpow]
    field_simp
    <;> ring

theorem scaled_gap_le (α C Δ T : ℝ) (hα : 0 < α) (hC : 0 < C)
    (hT : T ≤ Δ / (α * C)) : α * C * T ≤ Δ := by
  have := (le_div_iff₀ (mul_pos hα hC)).mp hT
  nlinarith

/-- A floor loses at most a factor two once at least two stages fit. -/
theorem floor_stage_budget (t : ℝ) (ht : 2 ≤ t) :
    t / 2 ≤ (⌊t⌋₊ : ℝ) ∧ (⌊t⌋₊ : ℝ) ≤ t := by
  have ht0 : 0 ≤ t := by linarith
  have hfloor := Nat.lt_floor_add_one t
  constructor
  · push_cast at hfloor
    linarith
  · exact Nat.floor_le ht0

/-- The two lower-bound branches combine without losing more than a factor two. -/
theorem combine_lower_bounds (Q n A c₁ c₂ : ℝ)
    (hn : 0 ≤ n) (hA : 0 ≤ A) (h₁ : c₁ * n ≤ Q) (h₂ : c₂ * A ≤ Q) :
    min c₁ c₂ / 2 * (n + A) ≤ Q := by
  have h₁' := mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) hn
  have h₂' := mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) hA
  nlinarith

/-- In the small-stage regime the claimed accuracy term is absorbed by `n`. -/
theorem small_stage_absorption (n stage K : ℝ) (hn : 0 ≤ n) (h : stage ≤ K) :
    n + n * stage ≤ (1 + K) * n := by
  have := mul_le_mul_of_nonneg_left h hn
  nlinarith

noncomputable def biasWork (n ρ s : ℝ) : ℝ := min n (ρ ^ (-2 : ℝ)) * ρ ^ s

theorem biasWork_eq_min (n ρ s : ℝ) (hρ : 0 < ρ) :
    biasWork n ρ s = min (n * ρ ^ s) (ρ ^ (s - 2)) := by
  rw [biasWork, min_mul_of_nonneg _ _ (Real.rpow_nonneg hρ.le s)]
  congr 1
  rw [← Real.rpow_add hρ]
  congr 1
  ring

/-- The bias is optimal precisely at the crossing of its two monotone branches. -/
theorem biasWork_optimal (n ρ ρ₀ s : ℝ)
    (hn : 0 ≤ n) (hρ : 0 < ρ) (hρ₀ : 0 < ρ₀)
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hbalance : n = ρ₀ ^ (-2 : ℝ)) :
    biasWork n ρ s ≤ biasWork n ρ₀ s := by
  have hcross : n * ρ₀ ^ s = ρ₀ ^ (s - 2) := by
    rw [hbalance, ← Real.rpow_add hρ₀]
    congr 1
    ring
  rw [biasWork_eq_min n ρ s hρ, biasWork_eq_min n ρ₀ s hρ₀, ← hcross,
    min_self]
  rcases le_total ρ ρ₀ with h | h
  · exact (min_le_left _ _).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hρ.le h hs) hn)
  · rw [hcross]
    exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos hρ₀ h (by linarith))

theorem optimal_bias_value (n s : ℝ) (hn : 0 < n) :
    biasWork n (n ^ (-(1 / 2 : ℝ))) s = n ^ (1 - s / 2) := by
  have hn0 := hn.le
  have hbal : (n ^ (-(1 / 2 : ℝ))) ^ (-2 : ℝ) = n := by
    rw [← Real.rpow_mul hn0]
    norm_num
  rw [biasWork, hbal, min_self, ← Real.rpow_mul hn0]
  conv_lhs => lhs; rw [← Real.rpow_one n]
  rw [← Real.rpow_add hn]
  congr 1
  ring

/-- The exponent claimed in the manuscript, with all real powers interpreted literally. -/
theorem optimized_rate (n A p : ℝ) (hn : 0 < n) :
    A * biasWork n (n ^ (-(1 / 2 : ℝ))) (1 / p) =
      A * n ^ (1 - 1 / (2 * p)) := by
  rw [optimal_bias_value n (1 / p) hn]
  congr 2
  ring

end FullJet
