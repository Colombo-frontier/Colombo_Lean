import FreshGradientMinimax.LabelBadProbability

/-! An explicit finite ambient dimension, chosen before the algorithm, makes
all collisions and all adaptive hidden projections have total mass at most 1/12.
This dimension is larger than the paper's Haar-frame dimension; the main
dimension-uniform minimax statements permit this alternative hard distribution. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def labelHidingMass (p : Parameters) (N : ℕ) : ℝ :=
  ((4 * N + 4 : ℕ) : ℝ) ^ 2 + (N : ℝ) * (4 * N + 4 : ℕ) *
    ((2 * pathHardRadius p.L p.μ p.ε (4 * N + 3)) ^ 2 /
      (pathHardFlatWidth p.L p.μ p.ε (4 * N + 3) / 2) ^ 2)

def labelHidingDimension (p : Parameters) (N : ℕ) : ℕ :=
  4 * N + 5 + ⌈12 * labelHidingMass p N⌉₊

theorem labelHidingDimension_size (p : Parameters) (N : ℕ) : 4 * N + 4 ≤ labelHidingDimension p N := by
  unfold labelHidingDimension
  omega

theorem labelHidingDimension_pos (p : Parameters) (N : ℕ) : 0 < labelHidingDimension p N := by
  have h := labelHidingDimension_size p N
  omega

instance labelHidingDimension_neZero (p : Parameters) (N : ℕ) : NeZero (labelHidingDimension p N) :=
  ⟨ne_of_gt (labelHidingDimension_pos p N)⟩

theorem labelHidingDimension_mass (p : Parameters) (N : ℕ) :
    12 * labelHidingMass p N ≤ (labelHidingDimension p N : ℝ) := by
  have hc : 12 * labelHidingMass p N ≤ (⌈12 * labelHidingMass p N⌉₊ : ℝ) := Nat.le_ceil _
  unfold labelHidingDimension
  push_cast
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

theorem labelHidingDimension_ratio (p : Parameters) (N : ℕ) :
    labelHidingMass p N / labelHidingDimension p N ≤ (1 / 12 : ℝ) := by
  have hD : (0 : ℝ) < labelHidingDimension p N := Nat.cast_pos.mpr (labelHidingDimension_pos p N)
  apply (div_le_iff₀ hD).mpr
  linarith [labelHidingDimension_mass p N]

theorem Algorithm.labelBad_one_twelfth (p : Parameters) (N : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm 1 (labelHidingDimension p N) Seed) (seed : Seed) :
    (𝔼 z : Fin (4 * N + 4) → Fin (labelHidingDimension p N),
      truthValue (¬ A.LabelGood p N z seed)) ≤ (1 / 12 : ℝ) := by
  have hb := A.expect_labelBad_le p N seed
  have he : ((4 * N + 4 : ℕ) : ℝ) ^ 2 / labelHidingDimension p N +
      (N : ℝ) * (4 * N + 4 : ℕ) *
        ((2 * pathHardRadius p.L p.μ p.ε (4 * N + 3)) ^ 2 /
          ((labelHidingDimension p N : ℝ) * (pathHardFlatWidth p.L p.μ p.ε (4 * N + 3) / 2) ^ 2)) =
      labelHidingMass p N / labelHidingDimension p N := by
    unfold labelHidingMass
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at hb
  exact hb.trans (labelHidingDimension_ratio p N)

end FreshGradientMinimax
