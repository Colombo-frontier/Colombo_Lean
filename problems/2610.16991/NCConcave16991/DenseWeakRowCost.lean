import NCConcave16991.DenseWeakGrid

/-!
# Explicit row-cost scale

This file keeps the floor in the definition of `rρ` and proves the linear-in-`n` bounds supplied
by the admissible grid bias.
-/

namespace NCConcave16991.DenseWeakHiding

noncomputable def rowCost (n : ℕ) (ρ : ℝ) : ℕ :=
  Nat.floor ((1 / 4096 : ℝ) * min (n : ℝ) ((ρ⁻¹) ^ 2))

theorem rowCost_bounds_of_invSq
    {n : ℕ} {ρ : ℝ}
    (hinvLower : (n : ℝ) / 4 ≤ (ρ⁻¹) ^ 2)
    (hinvUpper : (ρ⁻¹) ^ 2 ≤ n) :
    (n : ℝ) / 16384 - 1 < rowCost n ρ ∧
      (rowCost n ρ : ℝ) ≤ (n : ℝ) / 4096 := by
  let x : ℝ := (1 / 4096 : ℝ) * min (n : ℝ) ((ρ⁻¹) ^ 2)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hminLower : (n : ℝ) / 4 ≤ min (n : ℝ) ((ρ⁻¹) ^ 2) := by
    exact le_min (by linarith) hinvLower
  have hminUpper : min (n : ℝ) ((ρ⁻¹) ^ 2) ≤ n := min_le_left _ _
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ (n : ℝ) / 4).trans hminLower)
  have hxLower : (n : ℝ) / 16384 ≤ x := by
    dsimp [x]
    nlinarith
  have hxUpper : x ≤ (n : ℝ) / 4096 := by
    dsimp [x]
    nlinarith
  have hfloorLower : x - 1 < (Nat.floor x : ℝ) := by
    have h := Nat.lt_floor_add_one x
    push_cast at h
    linarith
  have hfloorUpper : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
  change (n : ℝ) / 16384 - 1 < Nat.floor x ∧
    (Nat.floor x : ℝ) ≤ (n : ℝ) / 4096
  exact ⟨by linarith, hfloorUpper.trans hxUpper⟩

theorem parityGrid_rowCost_bounds {n : ℕ} (hn : 256 ≤ n) :
    let ρ : ℝ := (parityRoundedSqrt n : ℝ) / n
    (n : ℝ) / 16384 - 1 < rowCost n ρ ∧
      (rowCost n ρ : ℝ) ≤ (n : ℝ) / 4096 := by
  dsimp only
  obtain ⟨hlower, hupper⟩ := parityRoundedSqrt_invSq_bounds hn
  exact rowCost_bounds_of_invSq hlower hupper

end NCConcave16991.DenseWeakHiding

/- Adapted from the local 0105_formalization/Manuscript0105/RowCost.lean. These analytic lemmas are reused for the cited dense weak hiding dependency; they do not assert its oracle lower bound. -/
