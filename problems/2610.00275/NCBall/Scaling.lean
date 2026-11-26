import Mathlib.Tactic

/-! # Explicit arithmetic underlying the complexity scales -/

namespace NCBall

/-- The exact factor suppressed by the Ω notation in (10.4) is 1/16. -/
theorem goldstein_complexity_substitution (d L Δ δ ε : ℝ)
    (hδ : δ ≠ 0) (hε : ε ≠ 0) :
    d * L ^ 2 * (ε / δ) * Δ / (2 * ε) ^ 4 =
      (1 / 16) * (d * L ^ 2 * Δ / (δ * ε ^ 3)) := by
  field_simp
  ring

theorem radius_substitution (Δ ε : ℝ) : Δ / (2 * ε) = (1 / 2) * (Δ / ε) := by
  ring

/-- The product of the stage depth and per-stage measurement scale, (9.8). -/
theorem product_scale (d L H Δ η a b : ℝ) :
    (a * (H * Δ / η ^ 2)) * (b * (d * L ^ 2 / η ^ 2)) =
      (a * b) * (d * L ^ 2 * H * Δ / η ^ 4) := by
  ring

theorem nat_floor_half {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  have hx0 : 0 ≤ x := by linarith
  have hfloor := Nat.floor_le hx0
  linarith

/-- Floors lose at most a factor 4 in the product once both scales exceed 2. -/
theorem floor_product_lower {x y : ℝ} (hx : 2 ≤ x) (hy : 2 ≤ y) :
    x * y / 4 ≤ ((⌊x⌋₊ * ⌊y⌋₊ : ℕ) : ℝ) := by
  have hprod := mul_le_mul (nat_floor_half hx) (nat_floor_half hy)
    (by linarith : 0 ≤ y / 2) (Nat.cast_nonneg ⌊x⌋₊)
  push_cast
  nlinarith

/-- Converting n transverse coordinates to d=n+1 loses at most a factor 2. -/
theorem transverse_dimension_half {n : ℕ} (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℝ) / 2 ≤ (n : ℝ) := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  linarith

theorem conditioning_constants {good success : ℝ}
    (hg : 7 / 8 ≤ good) (hs : success ≤ 1 / 4) :
    success / good ≤ 2 / 7 ∧ success / good < 1 / 2 := by
  have hg0 : 0 < good := by linarith
  constructor
  · apply (div_le_iff₀ hg0).2
    linarith
  · apply (div_lt_iff₀ hg0).2
    linarith

end NCBall
