import FreshGradientMinimax.PrimalLabelBadEvents

/-! A finite ambient dimension chosen before the algorithm controls all raw
label collisions, hidden query projections, and the unrestricted final output. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def primalLabelHidingMass (n N : ℕ) (L ε μ : ℝ) : ℝ :=
  (((n + 1) + (n + n) : ℕ) : ℝ) ^ 2 + (N + 1 : ℝ) * ((n + 1) + (n + n) : ℕ) *
    (primalCompressionRadius n L ε ^ 2 / (primalLengthScale L ε / 4) ^ 2) +
    (N : ℝ) * ((n + 1) + (n + n) : ℕ) *
      (paperDualProtectionRadius n μ (primalValueScale L ε) ^ 2 / primalLengthScale L ε ^ 2)

def primalLabelDimension (n N : ℕ) (L ε μ : ℝ) : ℕ :=
  (n + 1) + (n + n) + 1 + ⌈12 * primalLabelHidingMass n N L ε μ⌉₊

theorem primalLabelDimension_size (n N : ℕ) (L ε μ : ℝ) :
    (n + 1) + (n + n) ≤ primalLabelDimension n N L ε μ := by
  unfold primalLabelDimension
  omega

theorem primalLabelDimension_pos (n N : ℕ) (L ε μ : ℝ) : 0 < primalLabelDimension n N L ε μ := by
  have h := primalLabelDimension_size n N L ε μ
  omega

instance primalLabelDimension_neZero (n N : ℕ) (L ε μ : ℝ) : NeZero (primalLabelDimension n N L ε μ) :=
  ⟨ne_of_gt (primalLabelDimension_pos n N L ε μ)⟩

theorem primalLabelDimension_mass (n N : ℕ) (L ε μ : ℝ) :
    12 * primalLabelHidingMass n N L ε μ ≤ (primalLabelDimension n N L ε μ : ℝ) := by
  have h := Nat.le_ceil (12 * primalLabelHidingMass n N L ε μ)
  unfold primalLabelDimension
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem primalLabelDimension_ratio (n N : ℕ) (L ε μ : ℝ) :
    primalLabelHidingMass n N L ε μ / primalLabelDimension n N L ε μ ≤ (1 / 12 : ℝ) := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr (primalLabelDimension_pos n N L ε μ) :
    (0 : ℝ) < primalLabelDimension n N L ε μ)).mpr
  linarith [primalLabelDimension_mass n N L ε μ]

theorem Algorithm.primalLabelBad_one_twelfth (n N : ℕ) {L ε μ : ℝ} (hL : 0 < L) (hε : 0 < ε)
    {Seed : Type*} [MeasurableSpace Seed]
    (A : Algorithm (primalLabelDimension n N L ε μ) (primalLabelDimension n N L ε μ) Seed)
    (σ : ℝ) (c : ℕ → Bool) (seed : Seed) :
    (𝔼 z : Fin ((n + 1) + (n + n)) → Fin (primalLabelDimension n N L ε μ),
      truthValue (A.PrimalLabelBad L ε μ σ c N seed z)) ≤ (1 / 12 : ℝ) := by
  have h := A.expect_primalLabelBad_le hL hε μ σ c N seed (n := n)
  have he : (((n + 1) + (n + n) : ℕ) : ℝ) ^ 2 / primalLabelDimension n N L ε μ +
        (N + 1 : ℝ) * ((n + 1) + (n + n) : ℕ) *
          (primalCompressionRadius n L ε ^ 2 / ((primalLabelDimension n N L ε μ : ℝ) * (primalLengthScale L ε / 4) ^ 2)) +
        (N : ℝ) * ((n + 1) + (n + n) : ℕ) *
          (paperDualProtectionRadius n μ (primalValueScale L ε) ^ 2 /
            ((primalLabelDimension n N L ε μ : ℝ) * primalLengthScale L ε ^ 2)) =
      primalLabelHidingMass n N L ε μ / primalLabelDimension n N L ε μ := by
    unfold primalLabelHidingMass
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact (h.trans_eq he).trans (primalLabelDimension_ratio n N L ε μ)

end FreshGradientMinimax
